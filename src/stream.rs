//! A high-performance, allocation-free, streaming JSON string unescaper.
//!
//! This module provides utilities to unescape JSON strings, with a focus on
//! performance and flexibility. It is designed to work with data sources that
//! deliver content in chunks, such as network sockets or file readers, without
//! requiring heap allocations or holding onto previous chunks.
//!
//! # Key Features
//!
//! - **Streaming Unescaping**: The main type, [`UnescapeStream`], processes byte
//!   slices incrementally. This is ideal for I/O-bound applications.
//! - **Zero Heap Allocations**: The entire process occurs on the stack, using a
//!   small internal buffer to "stitch" together escape sequences that are split
//!   across chunk boundaries.
//! - **Data-Source Agnostic**: The API uses a "push" model. You provide
//!   byte slices to the unescaper as you receive them, allowing the caller to
//!   reuse their input buffers.
//! - **Robust Error Handling**: Reports detailed errors, including the position
//!   and kind of failure.
//!
//! # How It Works
//!
//! The core of the streaming logic is the [`UnescapeStream`] struct. When you
//! process a slice using [`unescape_next`](UnescapeStream::unescape_next), it returns
//! a tuple containing two parts:
//!
//! 1.  An `Option<Result<char, UnescapeError>>`: This handles the "continuity"
//!     between the previous slice and the current one. It will be `Some(_)` only if
//!     the previous slice ended with an incomplete escape sequence that was
//!     resolved by the start of the new slice. The `Result` will contain the
//!     unescaped character on success or an error if the combined bytes form an
//!     invalid sequence.
//! 2.  An `UnescapeNext` iterator: This iterator yields the unescaped parts
//!     for the remainder of the current slice.
//!
//! After processing all slices, you **must** call [`finish`](UnescapeStream::finish) to check
//! for any leftover partial escape sequences, which would indicate a malformed
//! JSON string at the end of the stream.
//!
//! # Example
//!
//! ```rust
//! use json_escape::{stream::UnescapeStream, token::UnescapedToken};
//!
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     // A JSON string split into multiple parts.
//!     // The surrogate pair `\uD83D\uDE00` (😀) is split across parts.
//!     let parts = vec![
//!         br#"{"message": "Hello, W\"orld! \uD83D"#.as_slice(),
//!         br#"\uDE00"}"#.as_slice(),
//!     ];
//!
//!     let mut unescaper = UnescapeStream::new();
//!     let mut unescaped_string = String::new();
//!
//!     for part in parts {
//!         // Process the next part of the stream.
//!         let (boundary_char, rest_of_part) = unescaper.try_unescape_next(part)?;
//!
//!         // 1. Handle the character that may have spanned the boundary.
//!         if let Some(boundary_char) = boundary_char {
//!             unescaped_string.push(boundary_char);
//!         }
//!
//!         // 2. Process the rest of the current part.
//!         for result in rest_of_part {
//!             let unescaped_part = result?;
//!             match unescaped_part {
//!                 UnescapedToken::Literal(literal) => {
//!                     unescaped_string.push_str(std::str::from_utf8(literal)?)
//!                 }
//!                 UnescapedToken::Unescaped(ch) => unescaped_string.push(ch),
//!             }
//!         }
//!     }
//!
//!     // IMPORTANT: Always call finish() to detect errors at the end of the stream.
//!     unescaper.finish()?;
//!
//!     assert_eq!(unescaped_string, r#"{"message": "Hello, W"orld! 😀"}"#);
//!
//!     Ok(())
//! }
//! ```

use core::convert::Infallible;
#[cfg(feature = "std")]
use std::vec::Vec;

use crate::{
    UnescapeError, UnescapeErrorKind,
    token::{UnescapeTokens, UnescapedToken, unescape},
};

/// A streaming JSON string unescaper that operates over byte slices.
///
/// This struct is the main entry point for streaming unescaping. It maintains
/// a small internal buffer to handle escape sequences that are split across
/// slice boundaries without requiring heap allocations.
///
/// See the [module-level documentation](self) for examples and more details.
#[derive(Debug, Clone)]
#[must_use = "UnescapeStream does nothing unless consumed"]
pub struct UnescapeStream {
    // A full surrogate pair escape `\uXXXX\uYYYY` is 12 bytes.
    // This buffer is large enough to hold it and any other partial escape.
    stitch_buf: [u8; 12],
    /// The number of valid bytes in `stitch_buf`.
    stitch_len: u8,
}

impl Default for UnescapeStream {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl UnescapeStream {
    /// Creates a new, empty `UnescapeStream`.
    #[inline]
    pub fn new() -> Self {
        Self {
            stitch_buf: [0; 12],
            stitch_len: 0,
        }
    }

    /// Processes the next byte slice, returning a fallible result.
    ///
    /// This is a convenience wrapper around [`UnescapeStream::unescape_next`]. Instead of returning
    /// an `Option<Result<...>>`, it "hoists" a potential boundary error into
    /// the main `Result`.
    ///
    /// This simplifies error handling, as you can use the `?` operator to handle
    /// errors from both the boundary character and the rest of the stream.
    ///
    /// # Returns
    ///
    /// - `Ok((Option<char>, UnescapeNext))` on success. The `Option<char>` contains
    ///   the successfully unescaped character from a boundary-spanning sequence.
    /// - `Err(UnescapeError)` if completing a boundary-spanning sequence results
    ///   in a parsing error.
    #[inline]
    pub fn try_unescape_next<'a, 'b, I: AsRef<[u8]> + ?Sized>(
        &'a mut self,
        next_part: &'b I,
    ) -> Result<(Option<char>, UnescapeNext<'a, 'b>), UnescapeError> {
        let (boundary_result, new) = self.unescape_next(next_part);
        let boundary_char = boundary_result.transpose()?;

        Ok((boundary_char, new))
    }

    /// Processes the next byte slice in the stream.
    ///
    /// This is the primary method for feeding data to the unescaper. It returns a tuple:
    ///
    /// 1.  An `Option<Result<char, UnescapeError>>` for the character that may have
    ///     spanned the boundary from the *previous* slice. `None` if the previous
    ///     slice ended cleanly.
    /// 2.  An `UnescapeNext` iterator for the remainder of the *current* slice.
    ///
    /// If the current slice ends with an incomplete escape sequence, that partial data is
    /// saved internally. It will be resolved on the next call to `unescape_next` again with
    /// the subsequent slice or reported as an error by `finish`.
    pub fn unescape_next<'a, 'b, I: AsRef<[u8]> + ?Sized>(
        &'a mut self,
        next_part: &'b I,
    ) -> (Option<Result<char, UnescapeError>>, UnescapeNext<'a, 'b>) {
        let mut next_part_slice = next_part.as_ref();
        let boundary_char = if self.stitch_len > 0 {
            // We have a partial escape from the previous chunk. Try to complete it.
            let old_stitch_len = self.stitch_len as usize;

            // Determine how many bytes to copy from the new chunk.
            // We copy enough to fill our buffer, which is sized for the longest escape.
            let needed = self.stitch_buf.len() - old_stitch_len;
            let to_copy = needed.min(next_part_slice.len());

            // Append bytes from the new chunk to our buffer.
            self.stitch_buf[old_stitch_len..old_stitch_len + to_copy]
                .copy_from_slice(&next_part_slice[..to_copy]);
            self.stitch_len += to_copy as u8;

            // Try to unescape the combined bytes.
            let mut unescaper = unescape(&self.stitch_buf[..self.stitch_len as usize]);
            let next = unescaper.next();

            match next {
                Some(Ok(token)) => {
                    // Success! The stitched part was resolved.
                    let total_consumed = (self.stitch_len as usize) - unescaper.remnant().len();
                    let consumed_from_next = total_consumed - old_stitch_len;
                    next_part_slice = &next_part_slice[consumed_from_next..];

                    let unescaped_char = match token {
                        UnescapedToken::Unescaped(c) => c,
                        _ => unreachable!("unescaper should produce a char from an escape"),
                    };

                    // Clear the buffer and return the resolved character.
                    self.stitch_len = 0;
                    Some(Ok(unescaped_char))
                }
                Some(Err(err)) => {
                    if err.kind == UnescapeErrorKind::UnexpectedEof {
                        // Still not enough data. The new data was consumed into our
                        // buffer but it wasn't enough to resolve the sequence.
                        // We will wait for the next chunk.
                        next_part_slice = &next_part_slice[to_copy..]; // Consume all we copied
                        None // No character or error to report yet.
                    } else {
                        // A definitive error occurred.
                        // To keep this function pure for a given `next_part`, we roll back
                        // the change to `stitch_len` so that another call with the same
                        // input will produce the same error. The bytes from `next_part_slice`
                        // are treated as lookahead only and are not consumed.
                        self.stitch_len = old_stitch_len as u8;
                        Some(Err(err))
                    }
                }
                None => {
                    // This is unreachable because the buffer is non-empty. The unescaper
                    // would either yield a chunk or an UnexpectedEof error.
                    unreachable!();
                }
            }
        } else {
            // The previous chunk ended cleanly.
            None
        };

        let iterator = UnescapeNext {
            stream: self,
            inner: UnescapeTokens::new(next_part_slice),
        };

        (boundary_char, iterator)
    }

    /// Finalizes the unescaping process, checking for leftover incomplete data.
    ///
    /// This method **must** be called after all slices have been processed. It checks
    /// if there is an incomplete escape sequence stored in its internal buffer. If so,
    /// it means the stream ended unexpectedly, and an `Err(UnescapeError)` is returned.
    ///
    /// This method consumes the `UnescapeStream`, preventing further use.
    pub fn finish(self) -> Result<(), UnescapeError> {
        if self.stitch_len > 0 {
            // If there are bytes left in the stitch buffer, it means the stream
            // ended mid-escape. We re-run the parser on just this fragment
            // to generate the correct EOF error.
            let buf = &self.stitch_buf[..self.stitch_len as usize];
            if let Some(Err(e)) = unescape(buf).next() {
                // We expect an EOF error here specifically.
                debug_assert_eq!(
                    e,
                    UnescapeError {
                        kind: UnescapeErrorKind::UnexpectedEof,
                        offset: self.stitch_len
                    }
                );
                return Err(e);
            }
        }
        Ok(())
    }

    /// Clears any partial escape sequence data from the internal buffer.
    ///
    /// You might call this after encountering a non-fatal error if you want to
    /// discard the invalid partial data and continue processing the stream from
    /// a fresh state.
    ///
    /// **Warning**: If you `clear()` the state after an error and then call
    /// `finish()` without processing more data, `finish()` will return `Ok(())`
    /// because the partial state that caused the original error has been erased.
    pub fn clear(&mut self) {
        self.stitch_len = 0;
    }

    /// Unescapes a stream of byte chunks from a source function to a destination function.
    ///
    /// This function acts as a driver for the [`UnescapeStream`]. It repeatedly calls a
    /// source function (`src`) to get the next chunk of data, unescapes it, and then
    /// calls a destination function (`dst`) for each resulting [`UnescapedToken`].
    ///
    /// This provides a flexible way to connect any data source (like a file reader or
    /// network socket) to any data sink without manually iterating.
    ///
    /// # Parameters
    ///
    /// - `self`: The `UnescapeStream` instance, which will be consumed.
    /// - `src`: A closure or function that, when called, returns the next chunk of
    ///   data as `Option<Result<B, SrcError>>`. It should return `Some(Ok(chunk))`
    ///   for data, `Some(Err(e))` for a source error, and `None` to signal the
    ///   end of the stream.
    /// - `dst`: A closure or function that receives an [`UnescapedToken`]. It should
    ///   return `Ok(())` on success or `Err(DstError)` on failure.
    ///
    /// # Errors
    ///
    /// Returns an [`UnescapeFnError`] if an error occurs at any point:
    /// - [`UnescapeFnError::Src`] if the `src` function returns an error.
    /// - [`UnescapeFnError::Unescape`] if the JSON string is malformed (e.g., an
    ///   invalid escape sequence or incomplete data at the end of the stream).
    /// - [`UnescapeFnError::Dst`] if the `dst` function returns an error.
    pub fn unescape_from_fn<Src, Dst, SrcError, DstError, B>(
        self,
        src: Src,
        dst: Dst,
    ) -> Result<(), UnescapeFnError<SrcError, DstError>>
    where
        Src: FnMut() -> Option<Result<B, SrcError>>,
        Dst: FnMut(UnescapedToken<'_>) -> Result<(), DstError>,
        B: AsRef<[u8]>,
    {
        self.unescape_from_source(
            FnMutChunkSource {
                closure: src,
                _phantom: core::marker::PhantomData,
            },
            dst,
        )
    }

    /// Processes a stream of byte chunks from a source and unescapes them to a destination.
    ///
    /// This function drives the unescaping process by repeatedly calling a `src`
    /// (source) to get a chunk of bytes, unescaping the data, and then passing
    /// the resulting `UnescapedToken`s to a `dst` (destination).
    ///
    /// This provides a flexible pipeline for connecting any byte source (e.g., a file
    /// or network stream) to any byte sink without manual iteration.
    ///
    /// # Parameters
    /// - `src`: A `ChunkSource` that provides the raw, escaped byte chunks.
    /// - `dst`: A closure that receives each `UnescapedToken` and processes it.
    ///
    /// # Errors
    /// This function returns an `UnescapeFnError` if an error occurs at any stage:
    /// - `UnescapeFnError::Src`: An error from the source (`src`).
    /// - `UnescapeFnError::Unescape`: The data is malformed (e.g., an invalid escape sequence).
    /// - `UnescapeFnError::Dst`: An error from the destination (`dst`).
    pub fn unescape_from_source<Src, Dst, SrcError, DstError>(
        mut self,
        mut src: Src,
        mut dst: Dst,
    ) -> Result<(), UnescapeFnError<SrcError, DstError>>
    where
        Src: ChunkSource<Error = SrcError>,
        Dst: FnMut(UnescapedToken<'_>) -> Result<(), DstError>,
    {
        while let Some(next) = src.next_chunk() {
            let next = next.map_err(UnescapeFnError::Src)?;
            let (boundary, next) = self
                .try_unescape_next(next.as_ref())
                .map_err(UnescapeFnError::Unescape)?;

            if let Some(ch) = boundary {
                dst(UnescapedToken::Unescaped(ch)).map_err(UnescapeFnError::Dst)?;
            }

            for token in next {
                let token = token.map_err(UnescapeFnError::Unescape)?;
                dst(token).map_err(UnescapeFnError::Dst)?;
            }
        }

        self.finish().map_err(UnescapeFnError::Unescape)
    }
}

/// An error that can occur during the `unescape_from_source` operation.
///
/// This enum consolidates errors from the three potential points of failure:
/// 1. Reading from the source (`Src`).
/// 2. The JSON unescaping process itself (`Unescape`).
/// 3. Writing to the destination (`Dst`).
#[derive(Clone, Debug)]
pub enum UnescapeFnError<Src, Dst> {
    /// An error occurred during the unescaping process.
    Unescape(UnescapeError),
    /// An error occurred while reading from the source.
    Src(Src),
    /// An error occurred while writing to the destination.
    Dst(Dst),
}

impl<Src, Dst: core::fmt::Display> core::fmt::Display for UnescapeFnError<Src, Dst>
where
    Src: core::fmt::Display,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            UnescapeFnError::Unescape(e) => write!(f, "unescape error: {e}"),
            UnescapeFnError::Src(e) => write!(f, "source error: {e}"),
            UnescapeFnError::Dst(e) => write!(f, "destination error: {e}"),
        }
    }
}

#[cfg(feature = "std")]
impl<Src, Dst> std::error::Error for UnescapeFnError<Src, Dst>
where
    Src: std::error::Error + 'static,
    Dst: std::error::Error + 'static,
{
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            UnescapeFnError::Unescape(e) => Some(e),
            UnescapeFnError::Src(e) => Some(e),
            UnescapeFnError::Dst(e) => Some(e),
        }
    }
}

impl From<UnescapeFnError<Infallible, Infallible>> for UnescapeError {
    fn from(value: UnescapeFnError<Infallible, Infallible>) -> Self {
        match value {
            UnescapeFnError::Unescape(unescape_error) => unescape_error,
            UnescapeFnError::Src(i) => match i {},
            UnescapeFnError::Dst(i) => match i {},
        }
    }
}

/// An iterator over the unescaped parts of a single byte slice.
///
/// This struct is created by [`UnescapeStream::unescape_next`].
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Debug)]
pub struct UnescapeNext<'a, 'b> {
    stream: &'a mut UnescapeStream,
    inner: UnescapeTokens<'b>,
}

impl<'a, 'b> Iterator for UnescapeNext<'a, 'b> {
    type Item = Result<UnescapedToken<'b>, UnescapeError>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.next() {
            // ASSUMPTION: Unfinished high surrogate will cause UnexpectedEof
            Some(Err(e)) if e.kind == UnescapeErrorKind::UnexpectedEof => {
                // The current chunk ends with an incomplete escape sequence.
                // Save the remnant for the next call to `unescape_next`.
                //
                // ASSUMPTION: UnescapeTokens will not update state on error.
                let remnant = self.inner.remnant();
                debug_assert!(!remnant.is_empty() && remnant[0] == b'\\', "{remnant:?}");
                debug_assert!(remnant.len() < self.stream.stitch_buf.len(), "{remnant:?}");

                // Copy the remnant and update the length.
                self.stream.stitch_buf[..remnant.len()].copy_from_slice(remnant);
                self.stream.stitch_len = remnant.len() as u8;

                // Stop iterating for this chunk.
                None
            }
            // A definitive error or a valid chunk.
            other => other,
        }
    }
}

// =============================================================================
// Traits
// =============================================================================

/// This trait is designed to handle byte streams efficiently, especially when the
/// source needs to borrow from an internal buffer between calls. A simple closure
/// (`FnMut() -> Option<Result<B, E>>`) cannot express this lifetime relationship,
/// as the returned slice would need to outlive the closure call itself. This trait
/// solves that by making the source a mutable object that you call repeatedly.
///
/// Async functionality can be achieved by the original API
pub trait ChunkSource {
    /// The type of error that can occur when reading a chunk.
    type Error;

    /// The type of chunk returned, which must implement AsRef<[u8]>
    type Chunk<'a>: AsRef<[u8]> + 'a
    where
        Self: 'a;

    /// Get the next chunk of bytes.
    ///
    /// Returns `None` when the source is exhausted, `Some(Ok(bytes))` for a successful chunk,
    /// or `Some(Err(e))` if an error occurred.
    ///
    /// The returned slice is valid until the next call to `next_chunk` or until the
    /// source is dropped.
    fn next_chunk<'a>(&'a mut self) -> Option<Result<Self::Chunk<'a>, Self::Error>>;
}

impl<T> ChunkSource for &mut T
where
    T: ChunkSource,
{
    type Error = T::Error;

    type Chunk<'a>
        = T::Chunk<'a>
    where
        Self: 'a;

    #[inline]
    fn next_chunk<'a>(&'a mut self) -> Option<Result<Self::Chunk<'a>, Self::Error>> {
        (*self).next_chunk()
    }
}

/// A `ChunkSource` that reads from any `std::io::Read` type.
///
/// This struct manages an internal buffer, which is filled with data on each read
/// operation. You can configure the buffer size to balance memory usage and I/O
/// performance.
#[cfg(feature = "std")]
pub struct ReadChunkSource<R, B> {
    reader: R,
    buffer: B,
}

#[cfg(feature = "std")]
impl<R, B> ReadChunkSource<R, B> {
    /// Creates a new `ReadChunkSource` with the given reader and a pre-allocated buffer.
    ///
    /// The size of the chunks read will be determined by the buffer's capacity.
    pub fn new(reader: R, buffer: B) -> Self {
        Self { reader, buffer }
    }

    /// Creates a new `ReadChunkSource` with the specified buffer capacity.
    ///
    /// This is a convenience method that creates a new `Vec<u8>` with the given
    /// capacity to use as the internal buffer.
    pub fn with_capacity(reader: R, capacity: usize) -> ReadChunkSource<R, Vec<u8>> {
        ReadChunkSource::new(reader, Vec::with_capacity(capacity))
    }
}

impl<R, B> ChunkSource for ReadChunkSource<R, B>
where
    R: std::io::Read,
    B: AsMut<[u8]>,
{
    type Error = std::io::Error;
    type Chunk<'a>
        = &'a [u8]
    where
        Self: 'a;

    #[inline]
    fn next_chunk<'a>(&'a mut self) -> Option<Result<Self::Chunk<'a>, Self::Error>> {
        let buffer = self.buffer.as_mut();
        // TODO; Make more robust (temporary error)
        match self.reader.read(buffer) {
            Ok(0) => None, // EOF
            Ok(n) => Some(Ok(&buffer[..n])),
            Err(e) => Some(Err(e)),
        }
    }
}

/// A `ChunkSource` implementation that wraps a mutable closure (`FnMut`).
///
/// This struct is generic over a lifetime `'s`, the closure type `F`,
/// the chunk type `B`, and the error type `E`. It correctly handles the
/// lifetime of the returned chunks, which are guaranteed to live at least
/// as long as the `'s` lifetime associated with the struct.
pub struct FnMutChunkSource<'s, F, B, E>
where
    F: FnMut() -> Option<Result<B, E>>,
    B: AsRef<[u8]> + 's,
{
    /// The wrapped closure that produces chunks.    
    closure: F,
    /// A marker to inform the compiler about the `'s` lifetime. This is
    /// necessary because the closure's return type `B` is tied to this
    /// lifetime, but the struct doesn't directly hold a reference with
    /// that lifetime.    
    _phantom: core::marker::PhantomData<&'s ()>,
}

impl<'s, F, B, E> FnMutChunkSource<'s, F, B, E>
where
    F: FnMut() -> Option<Result<B, E>>,
    B: AsRef<[u8]> + 's,
{
    /// Creates a new `FnMutChunkSource`.
    ///
    /// This function takes a closure `F` that will be used to generate chunks. The
    /// closure must return `Option<Result<B, E>>`, where `B` is a type that can be
    /// borrowed as a `&[u8]` and `E` is the error type.    
    pub fn new(closure: F) -> Self {
        FnMutChunkSource {
            closure,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<'s, F, B, E> ChunkSource for FnMutChunkSource<'s, F, B, E>
where
    F: FnMut() -> Option<Result<B, E>>,
    B: AsRef<[u8]> + 's,
{
    type Error = E;
    type Chunk<'a>
        = B
    where
        Self: 'a;

    fn next_chunk<'a>(&'a mut self) -> Option<Result<Self::Chunk<'a>, Self::Error>> {
        (self.closure)()
    }
}

// Here we test our assumptions
#[cfg(test)]
mod assumptions_tests {
    use super::*;

    // Test that partial surrogate isn't lone-surrogate but
    // actually EOF
    #[test]
    fn insufficient_data_is_not_lone_surrogate() {
        let mut unescaper = unescape(br"\uD83D");
        assert_eq!(
            unescaper.next().unwrap().unwrap_err(),
            UnescapeError {
                kind: UnescapeErrorKind::UnexpectedEof,
                offset: 6
            }
        );

        let mut unescaper = unescape(br"\uD83D\");
        assert_eq!(
            unescaper.next().unwrap().unwrap_err(),
            UnescapeError {
                kind: UnescapeErrorKind::UnexpectedEof,
                offset: 7
            }
        );
    }

    #[test]
    fn lone_surrogate_is_not_eof() {
        let mut unescaper = unescape(br"\uD83Da");
        assert_eq!(
            unescaper.next().unwrap().unwrap_err(),
            UnescapeError {
                kind: UnescapeErrorKind::LoneSurrogate(crate::LoneSurrogateError {
                    surrogate: 0xD83D
                }),
                offset: 6
            }
        );
    }

    #[test]
    fn unescape_does_not_commit_on_error() {
        let err_input = br"\uD83D";
        let mut unescaper = unescape(err_input);
        let err = unescaper.next().unwrap().unwrap_err();
        assert_eq!(
            err,
            UnescapeError {
                kind: UnescapeErrorKind::UnexpectedEof,
                offset: 6
            }
        );

        assert_eq!(unescaper.remnant(), err_input);
    }

    #[test]
    fn unescape_keeps_erroring() {
        // This tests that an error is sticky.
        let err_input = br"\z";
        let mut unescaper = unescape(err_input);
        let err_1 = unescaper.next().unwrap().unwrap_err();
        // The iterator should continue to yield the same error.
        let err_2 = unescaper.next().unwrap().unwrap_err();

        assert_eq!(err_1, err_2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{str, string::String, vec::Vec};

    /// Helper to run a stream test and collect the output into a string.
    fn run_stream_test<I, S>(parts: I) -> Result<String, UnescapeError>
    where
        I: IntoIterator<Item = S>,
        S: AsRef<[u8]>,
    {
        let unescaper = UnescapeStream::new();
        let mut parts = parts.into_iter();
        let mut output = String::new();

        unescaper.unescape_from_fn::<_, _, Infallible, Infallible, _>(
            || parts.next().map(Ok),
            |token| {
                match token {
                    UnescapedToken::Unescaped(c) => output.push(c),
                    UnescapedToken::Literal(s) => output.push_str(str::from_utf8(s).unwrap()),
                }
                Ok(())
            },
        )?;

        Ok(output)
    }

    #[test]
    fn test_single_chunk_no_escapes() {
        let parts = [br"hello world"];
        assert_eq!(run_stream_test(parts).unwrap(), "hello world");
    }

    #[test]
    fn test_single_chunk_with_escapes() {
        let parts = [br#"hello \"world\t\n\\"#];
        assert_eq!(run_stream_test(parts).unwrap(), "hello \"world\t\n\\");
    }

    #[test]
    fn test_multiple_chunks_no_escapes() {
        let parts = [&br"hello "[..], &br"world"[..]];
        assert_eq!(run_stream_test(parts).unwrap(), "hello world");
    }

    #[test]
    fn test_empty_chunks() {
        let parts = [
            &br"hello"[..],
            &br""[..],
            &br" "[..],
            &br""[..],
            &br"world"[..],
        ];
        assert_eq!(run_stream_test(parts).unwrap(), "hello world");
    }

    #[test]
    fn test_split_before_escape() {
        let parts = [&br"hello"[..], &br"\nworld"[..]];
        assert_eq!(run_stream_test(parts).unwrap(), "hello\nworld");
    }

    #[test]
    fn test_split_during_simple_escape() {
        let parts = [&br"hello\"[..], &br"nworld"[..]];
        assert_eq!(run_stream_test(parts).unwrap(), "hello\nworld");
    }

    #[test]
    fn test_split_during_unicode_escape() {
        // Euro symbol € is U+20AC
        let parts = [&br"price: \u20"[..], &br"AC"[..]];
        assert_eq!(run_stream_test(parts).unwrap(), "price: €");
    }

    #[test]
    fn test_split_during_surrogate_pair() {
        // Grinning face 😀 is U+1F600 -> \uD83D\uDE00
        let parts = [&br"emoji: \uD83D"[..], &br"\uDE00"[..]];
        assert_eq!(run_stream_test(parts).unwrap(), "emoji: 😀");
    }

    #[test]
    fn test_split_between_surrogate_pair_halves() {
        let parts = [&br"emoji: \uD83D\"[..], &br"uDE00"[..]];
        assert_eq!(run_stream_test(parts).unwrap(), "emoji: 😀");
    }

    #[test]
    fn test_split_in_second_surrogate() {
        // Grinning face 😀 is U+1F600 -> \uD83D\uDE00
        let parts = [&br"emoji: \uD83D\uDE"[..], &br"00"[..]];
        assert_eq!(run_stream_test(parts).unwrap(), "emoji: 😀");
    }

    #[test]
    fn test_tiny_chunks_across_surrogate_pair() {
        // emoji: 😀 (\uD83D\uDE00)
        let parts = [
            br"e", br"m", br"o", br"j", br"i", br":", br" ", br"\", br"u", br"D", br"8", br"3",
            br"D", br"\", br"u", br"D", br"E", br"0", br"0",
        ];
        assert_eq!(run_stream_test(parts).unwrap(), "emoji: 😀");
    }

    #[test]
    fn test_finish_success() {
        let mut unescaper = UnescapeStream::new();
        let (boundary, rest) = unescaper.unescape_next(br"hello");
        assert!(boundary.is_none());
        assert_eq!(
            rest.map(|r| r.unwrap()).collect::<Vec<UnescapedToken>>(),
            alloc::vec![UnescapedToken::Literal(br"hello")]
        );

        let (boundary, rest) = unescaper.unescape_next(br" world");
        assert!(boundary.is_none());
        assert_eq!(
            rest.map(|r| r.unwrap()).collect::<Vec<UnescapedToken>>(),
            alloc::vec![UnescapedToken::Literal(br" world")]
        );

        // Now finish it, it should be successful.
        assert!(unescaper.finish().is_ok());
    }

    #[test]
    fn test_finish_error_on_incomplete_escape() {
        let mut unescaper = UnescapeStream::new();
        let (_, next) = unescaper.unescape_next(br"hello\");
        // drain next
        next.for_each(|r| {
            r.unwrap();
        });
        let err = unescaper.finish().unwrap_err();
        assert_eq!(err.kind, UnescapeErrorKind::UnexpectedEof);
    }

    #[test]
    fn test_finish_error_on_incomplete_unicode() {
        let mut unescaper = UnescapeStream::new();
        let (_, next) = unescaper.unescape_next(br"hello\u12");
        // drain next
        next.for_each(|r| {
            r.unwrap();
        });
        let err = unescaper.finish().unwrap_err();
        assert_eq!(err.kind, UnescapeErrorKind::UnexpectedEof);
    }

    #[test]
    fn test_error_across_boundary_invalid_escape() {
        let parts = [&br"oh\"[..], &br"z"[..]];
        let err = run_stream_test(parts).unwrap_err();
        assert_eq!(
            err.kind,
            UnescapeErrorKind::InvalidEscape(crate::InvalidEscapeError { found: b'z' })
        )
    }

    #[test]
    fn test_error_across_boundary_lone_surrogate() {
        // High surrogate followed by non-low-surrogate
        let parts = [&br"\uD83D"[..], &br"abc"[..]];
        let err = run_stream_test(parts).unwrap_err();
        assert_eq!(
            err.kind,
            UnescapeErrorKind::LoneSurrogate(crate::LoneSurrogateError { surrogate: 0xD83D })
        );
    }

    #[test]
    fn test_error_across_boundary_not_low_surrogate() {
        // High surrogate followed by another valid escape that is not a low surrogate
        let parts = [&br"\uD83D"[..], &br"\u0020"[..]]; // \u0020 is a space
        let err = run_stream_test(parts).unwrap_err();
        assert_eq!(
            err.kind,
            UnescapeErrorKind::LoneSurrogate(crate::LoneSurrogateError { surrogate: 0xD83D })
        );
    }

    #[test]
    fn test_clear_after_error() {
        let mut unescaper = UnescapeStream::new();
        let (_, next) = unescaper.try_unescape_next("abc\\").unwrap();

        // drain next
        next.for_each(|r| {
            r.unwrap();
        });

        // This will now cause an error across the boundary
        let err = unescaper.try_unescape_next(br"z").unwrap_err();
        assert_eq!(
            err.kind,
            UnescapeErrorKind::InvalidEscape(crate::InvalidEscapeError { found: b'z' })
        );

        // After the error, the internal state contains the partial data that caused it.
        // Finishing it would report an error. We use clone() to check without consuming.
        assert!(unescaper.clone().finish().is_err());

        // But if we clear it, the state is reset.
        unescaper.clear();
        assert!(unescaper.clone().finish().is_ok());

        // And we can continue processing new data.
        let mut output = String::new();
        let (boundary, rest) = unescaper.try_unescape_next(br"good data").unwrap();
        assert!(boundary.is_none());
        for token in rest {
            match token {
                Ok(UnescapedToken::Literal(literal)) => {
                    output.push_str(str::from_utf8(literal).unwrap())
                }
                _ => unreachable!(),
            }
        }
        assert_eq!(output, "good data");
    }

    #[test]
    fn test_error_after_successful_boundary() {
        let mut unescaper = UnescapeStream::new();
        // First part is an incomplete surrogate
        let (_, mut rest) = unescaper.unescape_next(br"\uD83D");
        assert!(rest.next().is_none()); // The iterator is consumed into the stitch buffer

        // Second part completes the surrogate but has an error after it
        let (boundary, mut rest) = unescaper.unescape_next(br"\uDE00\z");

        // The boundary char should be resolved correctly
        let boundary_char = boundary.unwrap().unwrap();
        assert_eq!(boundary_char, '😀');

        // The next token from the iterator should be the error
        let err = rest.next().unwrap().unwrap_err();
        assert_eq!(
            err.kind,
            UnescapeErrorKind::InvalidEscape(crate::InvalidEscapeError { found: b'z' })
        );

        // Since the error did not happen at the EOF of the chunk,
        // the stitch buffer is empty.
        assert_eq!(unescaper.stitch_len, 0);

        // Therefore, finishing the stream now should be OK, as there's no partial data.
        // The error was contained entirely within the second chunk.
        assert!(unescaper.finish().is_ok());
    }

    #[test]
    fn test_unescape_from_source_src_error() {
        let unescaper = UnescapeStream::new();
        let mut parts = alloc::vec![Ok(b"hello".as_slice()), Err("read error")].into_iter();
        let result =
            unescaper.unescape_from_fn(|| parts.next(), |_| -> Result<(), Infallible> { Ok(()) });
        match result {
            Err(UnescapeFnError::Src("read error")) => (), // pass
            _ => panic!("Expected a source error"),
        }
    }

    #[test]
    fn test_unescape_from_source_dst_error() {
        let unescaper = UnescapeStream::new();
        let mut parts = alloc::vec![Result::<_, ()>::Ok("hello")].into_iter();
        let result = unescaper.unescape_from_fn(
            || parts.next(),
            |_| -> Result<(), &str> { Err("write error") },
        );
        match result {
            Err(UnescapeFnError::Dst("write error")) => (), // pass
            _ => panic!("Expected a destination error"),
        }
    }
}
