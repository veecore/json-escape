//! # Streaming JSON String Escape/Unescape
//!
//! Welcome to a highly efficient, `no_std` compatible library for handling JSON string escaping and unescaping. This crate provides iterator-based tools that process strings on the fly, avoiding heap allocations for the entire result. It's designed for performance-critical applications, such as parsing large JSON files or working in memory-constrained environments. ⚡
//!
//! The core of the library is two iterator structs:
//! - **[`Escape`]**: Takes a string slice (`&str`) and yields escaped string slices ready for JSON serialization.
//! - **[`Unescape`]**: Takes a byte slice (`&[u8]`) representing the content of a JSON string and yields the decoded byte slices.
//!
//! ## Key Features
//! - **Zero-Copy Slicing**: For sequences of characters that don't need modification, the iterators yield slices that borrow directly from the input, avoiding unnecessary data copying.
//! - **Comprehensive JSON Support**: Correctly handles all standard JSON escapes: `\"`, `\\`, `\/`, `\b`, `\f`, `\n`, `\r`, `\t`.
//! - **Full Unicode Handling**: Correctly decodes `\uXXXX` sequences, including full support for UTF-16 surrogate pairs (e.g., `\uD83D\uDE00` for `😀`).
//! - **Robust Error Handling**: The `Unescape` iterator returns descriptive errors (`UnescapeError`) for invalid or truncated escape sequences, making debugging straightforward.
//! - **Allocation Control** (with `alloc` feature): Provides convenient methods to collect the iterator's output into owned types like `String` or `Cow<str>`.
//! - **`std::io` Integration** (with `std` feature): The `Unescape` iterator implements `std::io::Read`, allowing it to be used as an efficient reader for I/O streams.
//!
//! ## Quick Start: Escaping a String
//!
//! ```
//! use json_escape::escape_str;
//!
//! let input = "Hello, \"world\"!\nThis contains a \\ backslash.";
//! let expected = r#"Hello, \"world\"!\nThis contains a \\ backslash."#;
//!
//! // The `escape_str` function returns an iterator.
//! let mut escaper = escape_str(input);
//!
//! // You can iterate over the chunks:
//! assert_eq!(escaper.next(), Some("Hello, "));
//! assert_eq!(escaper.next(), Some(r#"\""#));
//! assert_eq!(escaper.next(), Some("world"));
//! // ...and so on.
//!
//! // Or, collect it into a String (requires the "alloc" feature).
//! // let escaped_string: String = escape_str(input).collect();
//! // assert_eq!(escaped_string, expected);
//! ```
//!
//! ## Quick Start: Unescaping a String
//!
//! ```
//! use json_escape::unescape;
//!
//! let input = r#"A 😀 emoji: \uD83D\uDE00 and a tab\t!"#;
//!
//! // The unescape iterator yields `Result<&[u8], _>`.
//! let unescaper = unescape(input);
//!
//! // With the "alloc" feature, you can decode it directly into a string.
//! let decoded_cow = unescaper.decode_utf8().unwrap();
//! assert_eq!(decoded_cow, "A 😀 emoji: 😀 and a tab\t!");
//! ```
//!
//! ## Performance and the `explicit` Module
//!
//! This crate is designed for high-performance, zero-allocation escaping and
//! unescaping. For most use cases, the functions in this root module provide the
//! best balance of ergonomics and speed.
//!
//! However, for users with extreme performance requirements, the [`explicit`]
//! module is provided. Its iterators yield structured `Chunk` data instead of
//! simple slices. As shown by benchmarks, this approach can be slightly faster,
//! especially on inputs with a high density of escape sequences. If you are
//! processing a very large volume of JSON strings in a tight loop, consider
//! using the `explicit` module for a potential performance boost.
#![no_std]
#![deny(missing_docs)]
#![cfg_attr(all(feature = "simd", nightly), feature(portable_simd))]

#[cfg(any(test, feature = "std"))]
extern crate std;

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(any(test, feature = "alloc"))]
use alloc::{borrow::Cow, string::String, vec::Vec};

use core::{
    char,
    fmt::{self, Write as _},
    iter::FusedIterator,
    str,
};

pub mod explicit;

// =============================================================================
// Escape Implementation
// =============================================================================

/// Creates a streaming JSON string escaper from a string slice.
///
/// The returned [`Escape`] iterator lazily processes the input string, yielding
/// slices that represent the escaped output.
///
/// # Examples
///
/// ```
/// use json_escape::escape_str;
///
/// let escaper = escape_str("a\nb");
/// let escaped_parts: Vec<_> = escaper.collect();
///
/// assert_eq!(escaped_parts, vec!["a", r#"\n"#, "b"]);
/// ```
#[inline]
pub fn escape_str(input: &str) -> Escape<'_> {
    Escape {
        bytes: input.as_bytes(),
    }
}

/// A streaming JSON string escaper that yields `&'a str` slices.
///
/// This struct is created by the [`escape_str`] function. It is an [`Iterator`]
/// that breaks the input string into chunks at each character that needs to be
/// escaped according to JSON rules.
///
/// - For sequences of safe characters, it yields a single borrowed slice (`&'a str`).
/// - For each character that must be escaped, it yields a `'static` slice
///   containing the escaped representation (e.g., `r#"\n"#`).
///
/// This approach is highly efficient as it avoids allocating a new string for the
/// entire output, processing the input in a streaming fashion.
///
/// ### Implemented Traits
/// - **`Iterator<Item = &'a str>`**: Allows you to process the escaped parts in a loop or with adapters.
/// - **`Display`**: Lets you write the escaped content directly to any formatter, like `println!` or a file, without intermediate allocation.
/// - **`Clone`**, **`Debug`**: Standard utility traits.
/// - **`PartialEq`**, **`PartialEq<B: AsRef<[u8]>>`**: Allows direct comparison of the escaped output. An `Escape` iterator is equal to another `Escape` or a byte slice if they produce an identical sequence of escaped bytes.
/// - **`From<Escape<'a>> for Cow<'a, str>`** (requires `alloc` feature): Provides an efficient way to convert the iterator into a potentially owned string.
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Escape<'a> {
    bytes: &'a [u8],
}

impl<'a> Iterator for Escape<'a> {
    type Item = &'a str;

    #[inline]
    fn next(&mut self) -> Option<&'a str> {
        if self.bytes.is_empty() {
            return None;
        }

        // Find the first byte that needs escaping.
        let pos = find_escape_char(self.bytes);

        match pos {
            // No escapable characters left; return the rest of the slice.
            None => {
                let s = self.bytes;
                self.bytes = &self.bytes[self.bytes.len()..];
                // SAFETY: The input was a valid &str, and we're returning the
                // whole remaining chunk, so it's still valid UTF-8.
                Some(unsafe { str::from_utf8_unchecked(s) })
            }
            // An escapable byte is at the beginning of the slice.
            Some(0) => {
                let byte = self.bytes[0];
                self.bytes = &self.bytes[1..];
                // The table lookup gives us a &'static str, which is a valid &'a str.
                //
                // Some(....unwrap()) is more correct
                ESCAPE_TABLE[byte as usize]
            }
            // Found an escapable byte after a safe prefix. Return the prefix.
            Some(p) => {
                let (prefix, rest) = self.bytes.split_at(p);
                self.bytes = rest;
                // SAFETY: The soundness of this operation is critical.
                // We are splitting the byte slice at the position of the first
                // character that requires escaping. All JSON characters that
                // require escaping (`"`, `\`, and control characters `\u0000`-`\u001F`)
                // are single-byte ASCII characters. Therefore, `p` is guaranteed
                // to be on a valid UTF-8 character boundary.
                Some(unsafe { str::from_utf8_unchecked(prefix) })
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.bytes.is_empty() {
            (0, Some(0))
        } else {
            // We'll yield at least 1 slice, and at most `len` slices if every byte is escaped.
            (1, Some(self.bytes.len()))
        }
    }
}

impl<'a> FusedIterator for Escape<'a> {}

impl fmt::Display for Escape<'_> {
    /// Allows direct formatting of the escaped string without intermediate allocation.
    ///
    /// This is very useful for writing the escaped output directly to a stream,
    /// such as a file or a network socket.
    ///
    /// # Example
    ///
    /// ```
    /// use json_escape::escape_str;
    ///
    /// let escaper = escape_str("User said: \"Hi!\"\n");
    /// let formatted = format!("{}", escaper);
    ///
    /// assert_eq!(formatted, r#"User said: \"Hi!\"\n"#);
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The `clone()` is cheap as it only copies a slice reference.
        for s in self.clone() {
            f.write_str(s)?
        }
        Ok(())
    }
}

impl fmt::Debug for Escape<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Escape").finish_non_exhaustive()
    }
}

impl<B: AsRef<[u8]> + ?Sized> PartialEq<B> for Escape<'_> {
    /// Compares the escaped output with any byte-slice-like object.
    ///
    /// This is primarily a convenience for testing, allowing you to check the
    /// fully concatenated result of an `Escape` iterator against a known `&str` or `&[u8]`.
    ///
    /// The notion of equality is based on the **output**, not the iterator's internal state.
    ///
    /// # Example
    ///
    /// ```
    /// use json_escape::escape_str;
    ///
    /// let escaper = escape_str("key\tvalue");
    ///
    /// // The escaper's output, when concatenated, equals the right-hand side.
    /// assert_eq!(escaper, r#"key\tvalue"#);
    /// ```
    fn eq(&self, other: &B) -> bool {
        let mut other = other.as_ref();
        for chunk in self.clone() {
            if !other.starts_with(chunk.as_bytes()) {
                return false;
            }
            other = &other[chunk.len()..];
        }
        // We completely searched it
        other.is_empty()
    }
}

impl<'a, 'b> PartialEq<Escape<'a>> for Escape<'b> {
    /// Compares two `Escape` iterators for equality.
    ///
    /// Two `Escape` iterators are considered equal if they'll produce the same **output**.
    /// It first performs a fast check on the underlying byte slices.
    fn eq(&self, other: &Escape<'a>) -> bool {
        // Fast path: if they are views into the same underlying data.
        self.bytes == other.bytes || chunks_eq(self.clone(), other.clone())
    }
}

#[cfg(feature = "alloc")]
impl<'a> From<Escape<'a>> for Cow<'a, str> {
    /// Efficiently collects the escaped parts into a `Cow<'a, str>`.
    ///
    /// This implementation is optimized to avoid allocation if possible:
    /// - If the input string requires **no escaping**, it returns `Cow::Borrowed`
    ///   with a slice of the original string.
    /// - If escaping is needed, it allocates a `String` and returns `Cow::Owned`.
    ///
    /// This is more efficient than `iter.collect::<String>()` because `collect`
    /// will always allocate.
    ///
    /// **Requires the `alloc` feature.**
    ///
    /// # Example
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use json_escape::escape_str;
    /// use std::borrow::Cow;
    ///
    /// // No escaping needed, so no allocation occurs.
    /// let cow_borrowed: Cow<str> = escape_str("plain text").into();
    /// assert!(matches!(cow_borrowed, Cow::Borrowed(_)));
    ///
    /// // Escaping is required, so a new String is allocated.
    /// let cow_owned: Cow<str> = escape_str("text with\nnewline").into();
    /// assert!(matches!(cow_owned, Cow::Owned(_)));
    /// assert_eq!(cow_owned, r#"text with\nnewline"#);
    /// # }
    /// ```
    fn from(mut iter: Escape<'a>) -> Self {
        match iter.next() {
            None => Cow::Borrowed(""),
            Some(first) => match iter.next() {
                None => Cow::Borrowed(first),
                Some(second) => {
                    let mut string =
                        String::with_capacity(first.len() + second.len() + iter.bytes.len());
                    string.push_str(first);
                    string.push_str(second);
                    string.extend(iter);
                    Cow::Owned(string)
                }
            },
        }
    }
}

// =============================================================================
// Unescape Implementation
// =============================================================================

/// Creates a streaming JSON string unescaper from a byte slice.
///
/// This function creates an iterator to unescape a byte slice representing the
/// **raw contents** of a JSON string, assuming the outer quotes have already
/// been removed.
///
/// For a more convenient way to handle complete JSON string literals (including
/// their surrounding `"` quotes), see the [`unescape_quoted`] function, which
/// automatically trims them.
///
/// The iterator will fail if the input contains invalid JSON escape sequences.
///
/// # Example
///
/// ```
/// use json_escape::{unescape, unescape_quoted};
///
/// // `unescape` works on the raw content, without quotes.
/// let content = r#"hello\tworld"#;
/// assert_eq!(unescape(content), "hello\tworld");
///
/// // If you pass a full JSON literal, the quotes are treated as literal characters.
/// let literal = r#""hello\tworld""#;
/// assert_eq!(unescape(literal), "\"hello\tworld\""); // Note the quotes in the output.
///
/// // For full literals like this, `unescape_quoted` is the recommended function.
/// assert_eq!(unescape_quoted(literal), "hello\tworld");
/// ```
#[inline]
pub fn unescape<I: AsRef<[u8]> + ?Sized>(input: &I) -> Unescape<'_> {
    Unescape::new(input.as_ref())
}

/// Creates a streaming JSON string unescaper, trimming enclosing quotes.
///
/// This function acts as a convenience wrapper around [`unescape`]. It first
/// inspects the input byte slice. If the slice begins and ends with a double-quote
/// character (`"`), these quotes are trimmed before the inner content is passed to
/// the unescaper.
///
/// If the input is not enclosed in quotes, this function behaves exactly like
/// [`unescape`]. This is useful for directly unescaping a complete JSON string
/// literal.
///
/// # Example
///
/// ```
/// use json_escape::{unescape, unescape_quoted};
///
/// // 1. With quotes: The outer quotes are trimmed before unescaping.
/// let unescaper = unescape_quoted(r#""hello\nworld""#);
/// assert_eq!(unescaper, b"hello\nworld");
///
/// // 2. Without quotes: Behaves exactly like the standard `unescape`.
/// let unescaper_no_quotes = unescape_quoted(r#"raw string"#);
/// assert_eq!(unescaper_no_quotes, b"raw string");
///
/// // 3. Mismatched quotes: The input is passed through as-is, quotes are not trimmed.
/// let mismatched_quotes = unescape_quoted(r#"hello""#);
/// assert_eq!(mismatched_quotes, b"hello\"");
///
/// // 4. Empty quoted string: Correctly results in an empty output.
/// let empty_quoted = unescape_quoted(r#""""#);
/// assert_eq!(empty_quoted, b"");
/// ```
#[inline]
pub fn unescape_quoted<I: AsRef<[u8]> + ?Sized>(input: &I) -> Unescape<'_> {
    let bytes = input.as_ref();
    let input = if bytes.len() >= 2 && bytes[0] == b'\"' && bytes[bytes.len() - 1] == b'\"' {
        &bytes[1..bytes.len() - 1]
    } else {
        bytes
    };

    unescape(input)
}

/// A streaming JSON string unescaper.
///
/// This struct is created by the [`unescape`] function. It implements an [`Iterator`]
/// that yields `Result<&'a [u8], UnescapeError>`, lazily decoding the input.
///
/// The iterator's output chunks are one of the following:
/// - **`Ok(&'a [u8])`**: A borrowed slice of the original input for a sequence of non-escaped bytes.
/// - **`Ok(&'static [u8])`**: A single-byte slice for a decoded escape sequence (e.g., `\n` becomes a slice containing `0x0A`).
///   For `\uXXXX` sequences, it yields a series of single-byte slices representing the UTF-8 encoding of the character.
/// - **`Err(UnescapeError)`**: An error indicating an invalid escape sequence, which halts further iteration as described below.
///
/// Because the iterator operates on bytes, you can use helper methods like
/// [`Unescape::decode_utf8`] or [`Unescape::decode_utf8_lossy`] to convert the
/// final result into a string.
///
/// # Error Handling
///
/// When the iterator encounters an invalid or incomplete escape, it returns an
/// `Err(UnescapeError)` describing the problem. The iterator then remains in an
/// **error state**: subsequent calls to `next()` will continue to return that same
/// error (i.e., the error is idempotent) and the iterator will not produce further
/// `Ok` chunks. This makes the behavior deterministic for callers that check the
/// first error and then stop.
///
/// Errors are classified by the precise condition encountered:
/// - **`InvalidEscape`**: The escape sequence uses an unknown escape character (e.g., `\q`).
/// - **`InvalidHex`**: A `\u` escape contains a non-hex character where a hex
///   digit was expected (e.g., `\uZ`).
/// - **`UnexpectedEof`**: The input ended before a complete escape sequence could be
///   read. This is used when there isn't enough input yet to decide whether the
///   sequence would be valid (for instance, an incomplete `\u` or a truncated
///   surrogate pair).
/// - **`LoneSurrogate`**: A complete `\uXXXX` was read, and it encodes a *high*
///   surrogate, but the following bytes definitively do not form a valid low
///   surrogate escape (for example, the next character is a space or any
///   non-`\u` character).
///
/// The difference between `UnexpectedEof` and `LoneSurrogate` is important:
/// - `UnexpectedEof` means **we couldn't decide** because the input ended too early.
/// - `LoneSurrogate` means **we did decide**—we saw a full `\uXXXX` high surrogate,
///   and the following input proves a pair will not follow.
///
/// #### Concrete examples
///
/// 1) A high surrogate followed by other data (not a `\u` low-surrogate) → `LoneSurrogate`:
///
/// ```rust
/// use json_escape::{unescape, UnescapeErrorKind, LoneSurrogateError};
///
/// let mut iter = unescape(r"\uD83D more data");
/// let err = iter.next().unwrap().unwrap_err();
/// assert!(matches!(err.kind(), UnescapeErrorKind::LoneSurrogate(LoneSurrogateError { surrogate: 0xD83D, .. })));
///
/// // Subsequent calls return the same error (iterator remains in the same error state).
/// let err = iter.next().unwrap().unwrap_err();
/// assert!(matches!(err.kind(), UnescapeErrorKind::LoneSurrogate(LoneSurrogateError { surrogate: 0xD83D, .. })));
/// ```
///
/// 2) An invalid escape character → `InvalidEscape`:
///
/// ```rust
/// use json_escape::{unescape, UnescapeErrorKind, InvalidEscapeError};
///
/// let mut iter = unescape(r"\q"); // `\q` is not a defined escape
/// let err = iter.next().unwrap().unwrap_err();
/// assert!(matches!(err.kind(), UnescapeErrorKind::InvalidEscape(InvalidEscapeError { found: b'q', .. })));
/// ```
///
/// 3) A malformed `\u` with a non-hex character → `InvalidHex`:
///
/// ```rust
/// use json_escape::{unescape, UnescapeErrorKind, InvalidHexError};
///
/// let mut iter = unescape(r"\uZ");
/// let err = iter.next().unwrap().unwrap_err();
/// assert!(matches!(err.kind(), UnescapeErrorKind::InvalidHex(InvalidHexError { found: b'Z', .. })));
/// ```
///
/// 4) Truncated / incomplete input ⇒ `UnexpectedEof`:
///
/// ```rust
/// use json_escape::{unescape, UnescapeErrorKind};
///
/// // a) truncated after the first \uXXXX (no following bytes yet)
/// let mut iter = unescape(r"\uD83D");
/// let err = iter.next().unwrap().unwrap_err();
/// assert!(matches!(err.kind(), UnescapeErrorKind::UnexpectedEof));
///
/// // b) starts a second \u but is truncated before hex digits
/// let mut iter = unescape(r"\uD83D\u");
/// let err = iter.next().unwrap().unwrap_err();
/// assert!(matches!(err.kind(), UnescapeErrorKind::UnexpectedEof));
///
/// // c) a lone backslash at end of input
/// let mut iter = unescape("\\");
/// let err = iter.next().unwrap().unwrap_err();
/// assert!(matches!(err.kind(), UnescapeErrorKind::UnexpectedEof));
/// ```
///
/// **Note**: This behavior intentionally mirrors common JSON parsers (e.g.,
/// `serde_json`, Go's `encoding/json`) for the EOF vs. semantic error distinction.
///
/// # Implemented Traits and Usage
///
/// - **`Iterator<Item = Result<&'a [u8], UnescapeError>>`**: The core trait for
///   processing the unescaped byte chunks.
/// - **`std::io::Read`** (requires `std` feature): Lets you use the unescaper as a
///   standard reader, perfect for integrating with other I/O APIs.
/// - **`TryFrom<Unescape<'a>> for Cow<'a, [u8]>`** (requires `alloc` feature): An
///   efficient way to collect the unescaped bytes, propagating any errors.
/// - **`Clone`**, **`Debug`**: Standard utility traits.
/// - **`PartialEq<B: AsRef<[u8]>>`**: Compares the fully unescaped output with a byte slice.
///
/// ## Reading Unescaped Bytes
///
/// With the `std` feature, `Unescape` can be used as any other `std::io::Read`
/// source. This is ideal for streaming and decoding large JSON string contents
/// without buffering the entire result in memory first.
///
/// ```rust
/// # #[cfg(feature = "std")] {
/// use json_escape::unescape;
/// use std::io::Read;
///
/// let mut reader = unescape(r#"chunk1\nchunk2"#);
/// let mut buf = Vec::new();
///
/// // Read all unescaped bytes from the iterator into the buffer.
/// reader.read_to_end(&mut buf).unwrap();
///
/// assert_eq!(buf, b"chunk1\nchunk2");
/// # }
/// ```
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Unescape<'a> {
    // The inner, chunk-based iterator.
    inner: explicit::Unescape<'a>,
    // scratch buffer for encoded UTF-8 bytes from a \uXXXX (or surrogate pair)
    unicode: [u8; 4],
    // We can eliminate this by depending on the header.
    unicode_len: u8, // how many bytes are valid in buf (0 means no pending)
    unicode_pos: u8, // how many bytes already emitted
}

impl<'a> Unescape<'a> {
    /// Construct from a byte slice which contains the characters inside the JSON string (no quotes).
    fn new(input: &'a [u8]) -> Self {
        Self {
            inner: explicit::Unescape { bytes: input },
            unicode: [0; 4],
            unicode_len: 0,
            unicode_pos: 0,
        }
    }

    #[inline]
    fn store_unicode(&mut self, ch: char) {
        self.unicode_len = ch.encode_utf8(&mut self.unicode).len() as u8;
        self.unicode_pos = 0;
    }

    #[inline]
    fn emit_pending_byte(&mut self) -> Option<u8> {
        if self.unicode_pos < self.unicode_len {
            let b = self.unicode[self.unicode_pos as usize];
            self.unicode_pos += 1;
            Some(b)
        } else {
            None
        }
    }

    /// Helper to emit the full unicode sequence and advance the internal position.
    #[inline]
    fn emit_unicode_as_str(&mut self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The check `unicode_pos > 0` is implicit from the call site.
        // The buffer is guaranteed to contain a valid UTF-8 sequence.
        let s = unsafe { str::from_utf8_unchecked(&self.unicode[..self.unicode_len as usize]) };
        f.write_str(s)?;

        // Mark the entire sequence as emitted.
        self.unicode_pos = self.unicode_len;

        Ok(())
    }

    fn _display_utf8(mut self, f: &mut fmt::Formatter<'_>, lossy: bool) -> fmt::Result {
        // The key insight: Chunks with more than one byte are *always*
        // borrowed from the original input, as all escaped characters
        // are yielded byte-by-byte.
        while let Some(result) = self.next() {
            match result {
                Ok(chunk) => {
                    if chunk.is_empty() {
                        continue;
                    }

                    // THE CORE LOGIC:
                    // Check if the iterator just yielded the *first byte* of a *multi-byte* sequence.
                    // - `unicode_pos == 1` means the first byte was just emitted.
                    // - `unicode_len > 1` means it's a multi-byte char (e.g., '¢', '😎').
                    if self.unicode_pos == 1 && self.unicode_len > 1 {
                        // This is our special case. We have the first byte in `chunk`, but
                        // it's more efficient to write the whole character at once from our buffer.
                        self.emit_unicode_as_str(f)?;
                        // The iterator will no longer yield the rest of the bytes. Since our helper
                        // has now advanced it. But to be sure...
                        self.unicode_pos = self.unicode_len;
                    } else {
                        // This is the normal case:
                        // 1. A large chunk borrowed from the original input.
                        // 2. A single-byte escape like `\n` or `\t`.
                        // 3. The last byte of a multi-byte sequence (or the only byte).
                        // In all these cases, we just need to display the chunk we received.
                        display_bytes_utf8(chunk, f, lossy)?;
                    }
                }
                Err(_) => {
                    if lossy {
                        break;
                    } else {
                        return Err(fmt::Error);
                    }
                }
            }
        }

        Ok(())
    }

    /// Decodes the unescaped byte stream into a UTF-8 string.
    ///
    /// This method consumes the iterator and collects all resulting byte chunks.
    /// If an unescaping error occurs, it's returned immediately. If the final
    /// sequence of bytes is not valid UTF-8, a UTF-8 error is returned.
    ///
    /// Like `From<Escape>`, this is optimized to return a `Cow::Borrowed` if no
    /// escapes were present in the input, avoiding allocation.
    ///
    /// **Requires the `alloc` feature.**
    ///
    /// # Example
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use json_escape::unescape;
    ///
    /// let input = r#"Emoji: \uD83D\uDE00"#;
    /// let cow = unescape(input).decode_utf8().unwrap();
    ///
    /// assert_eq!(cow, "Emoji: 😀");
    /// # }
    /// ```
    #[cfg(feature = "alloc")]
    pub fn decode_utf8(self) -> Result<Cow<'a, str>, DecodeUtf8Error> {
        match self.try_into().map_err(DecodeUtf8Error::Unescape)? {
            Cow::Borrowed(bytes) => str::from_utf8(bytes)
                .map(Cow::Borrowed)
                .map_err(DecodeUtf8Error::Utf8),
            Cow::Owned(bytes) => String::from_utf8(bytes)
                .map(Cow::Owned)
                .map_err(|e| DecodeUtf8Error::Utf8(e.utf8_error())),
        }
    }

    /// Decodes the unescaped byte stream lossily into a UTF-8 string.
    ///
    /// This is similar to [`Unescape::decode_utf8`] but replaces any invalid UTF-8 sequences
    /// with the replacement character (U+FFFD) instead of returning an error.
    ///
    /// An `UnescapeError` can still be returned if the JSON escaping itself is invalid.
    ///
    /// **Requires the `alloc` feature.**
    #[cfg(feature = "alloc")]
    pub fn decode_utf8_lossy(self) -> Result<Cow<'a, str>, UnescapeError> {
        Ok(decode_utf8_lossy(self.try_into()?))
    }

    /// Returns a wrapper that implements [`fmt::Display`].
    ///
    /// This allows an `Unescape` iterator to be used directly with formatting
    /// macros like `println!`, `format!`, etc. It writes the unescaped content
    /// directly to the formatter's buffer, **avoiding any heap allocations**.
    ///
    /// The iterator is consumed, and the resulting unescaped string is written
    /// to the formatter. Any invalid JSON escape sequences or invalid UTF-8 will
    /// cause a `fmt::Error`. **You should be cautious when using this method
    /// with the `format!` macro, as a `fmt::Error` from us will cause the macro
    /// to panic**.
    ///
    /// For a more robust alternative that will not panic on `UnescapeError` or
    /// invalid bytes, consider using [`Unescape::display_utf8_lossy`] instead.
    ///
    /// This method is a **zero-allocation** alternative to [`Unescape::decode_utf8`],
    /// which might allocate a `String` to return the unescaped content.
    ///
    /// # Example
    ///
    /// ```
    /// use json_escape::unescape;
    ///
    /// let original = r#"Hello, \uD83C\uDF0E!"#;
    /// let unescaper = unescape(original);
    ///
    /// let formatted = format!("{}", unescaper.display_utf8());
    /// assert_eq!(formatted, "Hello, 🌎!");
    /// ```
    pub fn display_utf8(self) -> DisplayUnescape<'a> {
        DisplayUnescape { inner: self }
    }

    /// Returns a wrapper that implements [`fmt::Display`] lossily.
    ///
    /// This method is an **allocation-free** way to write unescaped content
    /// to a formatter. It handles invalid JSON escape sequences and invalid
    /// UTF-8 gracefully, making it a "lossy" operation.
    ///
    /// - **Invalid JSON escape sequences:** Instead of causing an error, the iterator
    ///   terminates without an error.
    /// - **Invalid UTF-8 bytes:** These are replaced with the Unicode
    ///   replacement character (U+FFFD).
    ///
    /// This method is the **zero-allocation** counterpart to [`Unescape::decode_utf8_lossy`].
    pub fn display_utf8_lossy(self) -> DisplayUnescapeLossy<'a> {
        DisplayUnescapeLossy { inner: self }
    }
}

impl<'a> Iterator for Unescape<'a> {
    type Item = Result<&'a [u8], UnescapeError>;

    fn next(&mut self) -> Option<Self::Item> {
        // If we have pending bytes, emit them first (fast).
        if let Some(s) = self.emit_pending_byte() {
            // s: &'static [u8] coerces to &'a [u8]
            return Some(Ok(byte_as_static_slice(s)));
        }

        match self.inner.next() {
            Some(Ok(chunk)) => {
                if let Some(ch) = chunk.unescaped {
                    self.store_unicode(ch);
                }
                Some(Ok(chunk.literal))
            }
            Some(Err(err)) => Some(Err(err)),
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // The maximum size is the remaining length of the underlying iter + pending_unicode
        let (lower, upper) = self.inner.size_hint();
        let upper = upper.map(|x| x + (self.unicode_len as usize));
        (lower, upper)
    }
}

impl<'a> FusedIterator for Unescape<'a> {}

#[cfg(feature = "std")]
impl std::io::Read for Unescape<'_> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let mut total_written = 0;
        let mut remaining_buf = buf;

        // Loop until the destination buffer is full or we are completely out of data.
        loop {
            // Priority 1: Drain any pending bytes from an unescaped character first.
            if self.unicode_pos < self.unicode_len {
                let pending_unicode =
                    &self.unicode[self.unicode_pos as usize..self.unicode_len as usize];
                let bytes_to_copy = pending_unicode.len().min(remaining_buf.len());

                remaining_buf[..bytes_to_copy].copy_from_slice(&pending_unicode[..bytes_to_copy]);
                self.unicode_pos += bytes_to_copy as u8;
                total_written += bytes_to_copy;
                remaining_buf = &mut remaining_buf[bytes_to_copy..];

                // If buffer is now full, we are done for this call.
                if remaining_buf.is_empty() {
                    break;
                }
            }
            if self.unicode_pos >= self.unicode_len {
                self.unicode_pos = 0;
                self.unicode_len = 0;
            }

            // Priority 2: Get and process a new chunk from the inner iterator.
            match self.inner.next() {
                Some(Ok(chunk)) => {
                    let bytes_to_copy = chunk.literal.len().min(remaining_buf.len());
                    if bytes_to_copy > 0 {
                        remaining_buf[..bytes_to_copy]
                            .copy_from_slice(&chunk.literal[..bytes_to_copy]);
                        total_written += bytes_to_copy;
                        remaining_buf = &mut remaining_buf[bytes_to_copy..];
                    }

                    // ### THE BACKTRACKING TRICK ###
                    // This block executes if the destination `buf` was filled before we could
                    // finish reading the `literal` part of the current chunk.
                    if bytes_to_copy < chunk.literal.len() {
                        // We must reconstruct the *entire unread portion of the stream*.
                        // This includes:
                        //   1. The rest of the literal (e.g., "de").
                        //   2. The original escaped sequence (e.g., "\\n").
                        //   3. The rest of the stream that followed (e.g., "fghi").
                        //
                        // These parts are all contiguous in the original input slice.
                        // We can create a new slice view over this memory using pointer arithmetic.

                        // SAFETY: This is safe for several reasons:
                        // 1. `chunk.literal` and `self.inner.bytes` are both derived from the same
                        //    original slice with lifetime `'a`. All memory is valid.
                        // 2. `new_start_ptr` points to the start of the unread literal part, a valid memory location.
                        // 3. `stream_end_ptr` points to the end of the stream that `self.inner.bytes` currently sees.
                        // 4. The resulting slice is therefore a valid, contiguous sub-slice of the original input.
                        unsafe {
                            // Pointer to the first byte of the unread part of the literal.
                            let new_start_ptr = chunk.literal.as_ptr().add(bytes_to_copy);

                            // Pointer to one byte past the end of the remaining stream.
                            // We don't set self.inner.bytes to &[] in explicit
                            let stream_end_ptr =
                                self.inner.bytes.as_ptr().add(self.inner.bytes.len());

                            // The new length is the distance between these two pointers.
                            let new_len = stream_end_ptr as usize - new_start_ptr as usize;

                            // Reset the inner iterator's slice to this reconstructed view.
                            self.inner.bytes = std::slice::from_raw_parts(new_start_ptr, new_len);
                        }

                        // Since the buffer is full, we must stop and return. The next `read` call
                        // will now correctly resume from the middle of the previous chunk.
                        break;
                    }

                    // If we get here, the entire literal was consumed. Now handle the unescaped char.
                    if let Some(ch) = chunk.unescaped {
                        let encoded = ch.encode_utf8(&mut self.unicode);
                        self.unicode_len = encoded.len() as u8;
                        // Loop to immediately process the newly buffered unicode bytes.
                        continue;
                    }
                }
                Some(Err(e)) => {
                    return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, e));
                }
                None => break, // Inner iterator is exhausted.
            }
        }

        Ok(total_written)
    }

    // We can provide an optimized version of read_to_end
    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> std::io::Result<usize> {
        let start_len = buf.len();

        // Now, efficiently consume the rest of the iterator
        for result in self {
            match result {
                Ok(chunk) => buf.extend_from_slice(chunk),
                Err(err) => return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, err)),
            }
        }

        Ok(buf.len() - start_len)
    }
}

impl fmt::Debug for Unescape<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Unescape").finish_non_exhaustive()
    }
}

impl<B: AsRef<[u8]> + ?Sized> PartialEq<B> for Unescape<'_> {
    /// Compares the unescaped output with a byte-slice-like object.
    ///
    /// An `Unescape` iterator is considered equal to a byte slice if it successfully
    /// unescapes to produce a sequence of bytes identical to that slice. If the
    /// iterator would produce an error, the comparison returns `false`.
    ///
    /// # Example
    ///
    /// ```
    /// use json_escape::unescape;
    ///
    /// let unescaper = unescape(r#"hello\nworld"#);
    /// assert_eq!(unescaper, b"hello\nworld");
    ///
    /// // An iterator that produces an error is not equal to any valid slice.
    /// let failing_unescaper = unescape(r#"\k"#);
    /// assert_ne!(failing_unescaper, b"k");
    /// ```
    fn eq(&self, other: &B) -> bool {
        let mut other = other.as_ref();
        for result in self.clone() {
            match result {
                Ok(chunk) => {
                    if !other.starts_with(chunk) {
                        return false;
                    }
                    other = &other[chunk.len()..];
                }
                Err(_) => return false, // An erroring iterator cannot be equal to a valid slice.
            }
        }
        other.is_empty()
    }
}

impl<B: AsRef<[u8]>> PartialEq<Unescape<'_>> for Result<B, UnescapeError> {
    /// Compares the unescaper's outcome with a `Result`.
    ///
    /// This implementation allows for precise testing of the `Unescape` iterator
    /// by comparing it against either a successful outcome (`Ok`) or a specific
    /// failure (`Err`).
    ///
    /// - If `result` is `Ok(bytes)`, the comparison is `true` only if the iterator
    ///   completes successfully and its concatenated output is identical to `bytes`.
    ///
    /// - If `result` is `Err(error)`, the comparison is `true` only if the iterator
    ///   produces the exact same `UnescapeError`.
    ///
    /// # Example
    ///
    /// ```
    /// use json_escape::{unescape, UnescapeError, InvalidEscapeError};
    ///
    /// // --- Success Case ---
    /// let unescaper = unescape(r#"hello\tworld"#);
    /// // The comparison is against an `Ok` variant.
    /// assert_eq!(Ok("hello\tworld"), unescaper);
    ///
    /// // --- Error Case ---
    /// let failing_unescaper = unescape(r#"invalid-\u"#);
    /// // We can assert that the iterator produces a specific error.
    /// # let unexpected_eof = unescape(r"\u").next().unwrap().unwrap_err();
    /// assert_eq!(Err::<&str, _>(unexpected_eof), failing_unescaper);
    /// ```
    fn eq(&self, unescape: &Unescape<'_>) -> bool {
        match self {
            Ok(expected_bytes) => unescape == expected_bytes,
            Err(expected_error) => {
                for result in unescape.clone() {
                    if let Err(actual_error) = result {
                        // The iterator's first error is its final outcome.
                        // It must match the expected error exactly.
                        return actual_error == *expected_error;
                    }
                }
                // `unescape` completed successfully, but an error was expected.
                false
            }
        }
    }
}

impl<'a, 'b> PartialEq<Unescape<'a>> for Unescape<'b> {
    /// Compares two `Unescape` iterators for equality based on their terminal result.
    ///
    /// The equality of two `Unescape` iterators is determined by the final `Result`
    /// that would be obtained if each iterator were fully consumed (e.g., by using `try_collect()`).
    ///
    /// The specific rules are as follows:
    ///
    /// 1.  **Error vs. Error**: If both iterators terminate with an `Err`, they are
    ///     considered **equal** if and only if their `UnescapeError`s are identical.
    ///     Any bytes successfully unescaped *before* the error are ignored in this case.
    /// 2.  **Success vs. Success**: If both iterators terminate with `Ok`, they are
    ///     considered **equal** if and only if the complete sequence of unescaped bytes
    ///     is identical for both.
    /// 3.  **Success vs. Error**: If one iterator terminates with `Ok` and the other
    ///     with `Err`, they are always **not equal**.
    ///
    /// # Example
    ///
    /// ```
    /// use json_escape::unescape;
    ///
    /// // Case 1: Both iterators produce the same error. They are equal,
    /// // even though their valid prefixes ("a" and "b") are different.
    /// let failing_a = unescape(r#"a\k"#);
    /// let failing_b = unescape(r#"b\k"#);
    /// assert_eq!(failing_a, failing_b);
    ///
    /// // Case 2: Both iterators succeed. Equality depends on the byte stream.
    /// let successful_a = unescape(r#"hello\nworld"#);
    /// let successful_b = unescape(r#"hello\nworld"#);
    /// assert_eq!(successful_a, successful_b);
    ///
    /// let successful_c = unescape(r#"different"#);
    /// assert_ne!(successful_a, successful_c);
    ///
    /// // Case 3: One succeeds and one fails. They are not equal.
    /// let succeeding = unescape(r#"stop"#);
    /// let failing = unescape(r#"stop\k"#);
    /// assert_ne!(succeeding, failing);
    ///
    /// // Case 4: Both iterators fail differently. They are not equal.
    /// let failing_a = unescape(r#"data:\k"#);
    /// let failing_b = unescape(r#"data:\"#);
    /// assert_ne!(failing_a, failing_b);
    /// ```
    fn eq(&self, other: &Unescape<'a>) -> bool {
        // Fast path: if they are views into the same underlying data with the same state.
        ((self.inner.bytes == other.inner.bytes)
            && (self.unicode == other.unicode)
            && (self.unicode_len == other.unicode_len)
            && (self.unicode_pos == other.unicode_pos))
            || {
                let mut a_error = None;
                let mut b_error = None;

                let mut a = self.clone().map_while(|result| match result {
                    Ok(ok) => Some(ok),
                    Err(err) => {
                        a_error = Some(err);
                        None
                    }
                });

                let mut b = other.clone().map_while(|result| match result {
                    Ok(ok) => Some(ok),
                    Err(err) => {
                        b_error = Some(err);
                        None
                    }
                });

                let streams_match = chunks_eq(&mut a, &mut b);

                // Drain the iterators to ensure the error state is captured,
                // especially if chunks_eq returned false early.
                // (e.g unescape("a\k") and unescape("b\k") which are actually
                // equal)
                a.for_each(|_| {});
                b.for_each(|_| {});

                match (a_error, b_error) {
                    // Both errored: equality depends only on the errors being the same.
                    (Some(a_err), Some(b_err)) => a_err == b_err,
                    // Both succeeded: equality depends on the byte streams having been identical.
                    (None, None) => streams_match,
                    // One errored and the other didn't: they are not equal.
                    _ => false,
                }
            }
    }
}

#[cfg(feature = "alloc")]
impl<'a> TryFrom<Unescape<'a>> for Cow<'a, [u8]> {
    type Error = UnescapeError;

    /// Efficiently collects the unescaped bytes into a `Cow<'a, [u8]>`.
    ///
    /// This implementation will return `Cow::Borrowed` if the original input contained
    /// no escape sequences, avoiding allocation. Otherwise, it returns `Cow::Owned`.
    ///
    /// If any `UnescapeError` is encountered during iteration, the operation
    /// halts and returns that error.
    ///
    /// **Requires the `alloc` feature.**
    fn try_from(mut value: Unescape<'a>) -> Result<Self, Self::Error> {
        match value.next() {
            None => Ok(Cow::Borrowed(b"")),
            Some(Ok(first)) => match value.next() {
                None => Ok(Cow::Borrowed(first)),
                Some(Ok(second)) => {
                    let mut buf =
                        Vec::with_capacity(first.len() + second.len() + value.inner.bytes.len());
                    buf.extend_from_slice(first);
                    buf.extend_from_slice(second);
                    for item in value {
                        buf.extend_from_slice(item?);
                    }
                    Ok(Cow::Owned(buf))
                }
                Some(Err(e)) => Err(e),
            },
            Some(Err(e)) => Err(e),
        }
    }
}

// =============================================================================
// DisplayUnescape Implementation
// =============================================================================

/// A wrapper for an [`Unescape`] iterator that implements [`fmt::Display`].
///
/// This struct is created by the [`Unescape::display_utf8()`] method. It allows for
/// printing the unescaped content directly to a formatter, which **avoids
/// any heap allocations**. The unescaping and UTF-8 decoding are performed on-the-fly as the
/// `fmt` method is called.
pub struct DisplayUnescape<'a> {
    inner: Unescape<'a>,
}

impl fmt::Display for DisplayUnescape<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.clone()._display_utf8(f, false)
    }
}

/// A wrapper for an [`Unescape`] iterator that implements [`fmt::Display`] lossily.
///
/// This struct is created by the [`Unescape::display_utf8_lossy()`] method. Like
/// `DisplayUnescape`, it performs its operation **without any heap allocations**.
///
/// This method differs from `display_utf8` in that it handles two types of
/// errors gracefully:
/// - Invalid JSON escape sequences will be ignored, and the iterator will
///   continue to completion without a `fmt::Error`.
/// - Invalid UTF-8 byte sequences will be replaced with the Unicode
///   replacement character (``, U+FFFD)
pub struct DisplayUnescapeLossy<'a> {
    inner: Unescape<'a>,
}

impl fmt::Display for DisplayUnescapeLossy<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Lossy mode: replace invalid sequences with U+FFFD and continue.
        self.inner.clone()._display_utf8(f, true)
    }
}

// =============================================================================
// Error Types
// =============================================================================

/// An error that can occur when decoding the final byte stream to a UTF-8 string.
#[derive(Copy, Eq, PartialEq, Clone, Debug)]
pub enum DecodeUtf8Error {
    /// The unescaped byte sequence was not valid UTF-8.
    Utf8(str::Utf8Error),
    /// An error occurred during the JSON unescaping process itself.
    Unescape(UnescapeError),
}

impl fmt::Display for DecodeUtf8Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DecodeUtf8Error::Utf8(e) => fmt::Display::fmt(e, f),
            DecodeUtf8Error::Unescape(e) => fmt::Display::fmt(e, f),
        }
    }
}

/// Details of an invalid escape sequence error.
#[derive(Copy, Eq, PartialEq, Clone, Debug)]
#[non_exhaustive]
pub struct InvalidEscapeError {
    /// The invalid character found after a `\`.
    pub found: u8,
}

/// Details of a lone UTF-16 surrogate error.
#[derive(Copy, Eq, PartialEq, Clone, Debug)]
#[non_exhaustive]
pub struct LoneSurrogateError {
    /// The 16-bit surrogate code point.
    pub surrogate: u16,
}

/// Details of an invalid hex digit error within a `\uXXXX` sequence.
#[derive(Copy, Eq, PartialEq, Clone, Debug)]
#[non_exhaustive]
pub struct InvalidHexError {
    /// The non-hex character that was found.
    pub found: u8,
}

impl fmt::Display for InvalidHexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "found invalid hex digit '0x{:02X}'", self.found)
    }
}

/// An error that can occur during the JSON string unescaping process.
#[derive(Copy, Eq, PartialEq, Clone, Debug)]
pub struct UnescapeError {
    /// The specific kind of unescaping error.
    pub(crate) kind: UnescapeErrorKind,
    /// The byte offset from the start of the escape sequence (`\`) where the
    /// error was detected.
    ///
    /// This is guaranteed to be less than 12, as the maximum escape sequence
    /// is `\uXXXX\uXXXX`.
    pub(crate) offset: u8,
}

impl UnescapeError {
    /// Returns the specific kind of error that occurred.
    ///
    /// This can be used to programmatically handle different error types,
    /// such as distinguishing between a malformed hex sequence and an
    /// invalid escape character.
    ///
    /// ### Example
    ///
    /// ```
    /// # use json_escape::{unescape, UnescapeErrorKind, InvalidHexError};
    /// let mut unescaper = unescape(r#"\u123Z"#);
    /// let err = unescaper.next().unwrap().unwrap_err();
    ///
    /// match err.kind() {
    ///     UnescapeErrorKind::InvalidHex(InvalidHexError { found, .. }) => {
    ///         // We can inspect the exact invalid character found.
    ///         assert_eq!(found, b'Z');
    ///     }
    ///     _ => panic!("Expected an InvalidHex error"),
    /// }
    /// ```
    pub fn kind(&self) -> UnescapeErrorKind {
        self.kind
    }

    /// Returns the byte offset from the start of the escape sequence (`\`)
    /// where the error was detected.
    ///
    /// - For `\x`, the offset is `1` (pointing to `x`).
    /// - For `\u123?`, the offset is `5` (pointing to `?`).
    /// - For a lone surrogate `\uD800`, the offset is `6` (pointing after the sequence).
    ///
    /// This is useful for providing detailed error messages that can point
    /// to the exact location of the problem in the source string.
    ///
    /// ### Example
    ///
    /// ```
    /// # use json_escape::unescape;
    /// let json_string_content = r#"bad escape \x here"#;
    /// let mut unescaper = unescape(json_string_content);
    ///
    /// // previous read
    /// // { ... }
    ///
    /// let err = unescaper.next().unwrap().unwrap_err();
    ///
    /// // The error occurred at the 'x', which is 1 byte after the '\'
    /// assert_eq!(err.offset(), 1);
    ///
    /// // You could use this to highlight the error in the original input
    /// let backslash_pos = json_string_content.find('\\').unwrap();
    /// let error_pos = backslash_pos + err.offset() as usize;
    /// assert_eq!(json_string_content.as_bytes()[error_pos], b'x');
    ///
    /// // The generated error message also includes this info.
    /// let expected_msg = "invalid escape: '\\0x78' at offset 1";
    /// assert_eq!(err.to_string(), expected_msg);
    /// ```
    pub fn offset(&self) -> u8 {
        self.offset
    }
}

/// The specific kind of error that can occur during JSON string unescaping.
///
/// This enum covers all possible failures described by the JSON standard for string contents.
#[derive(Copy, Eq, PartialEq, Clone, Debug)]
#[non_exhaustive]
pub enum UnescapeErrorKind {
    /// Found a backslash followed by an unexpected character (e.g., `\x`).
    InvalidEscape(InvalidEscapeError),
    /// Found `\u` but the following characters were not 4 valid hex digits.
    InvalidHex(InvalidHexError),
    /// Input ended unexpectedly while parsing an escape sequence (e.g., `\u12`).
    UnexpectedEof,
    /// The `\u` sequence yielded a lone high or low surrogate without a matching pair.
    LoneSurrogate(LoneSurrogateError),
}

impl fmt::Display for UnescapeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            UnescapeErrorKind::InvalidEscape(e) => {
                write!(
                    f,
                    "invalid escape: '\\0x{:02X}' at offset {}",
                    e.found, self.offset
                )
            }
            UnescapeErrorKind::InvalidHex(ref s) => {
                write!(f, "{} at offset {}", s, self.offset)
            }
            UnescapeErrorKind::UnexpectedEof => {
                write!(
                    f,
                    "unexpected end of input while parsing escape sequence, expected character at offset {}",
                    self.offset
                )
            }
            UnescapeErrorKind::LoneSurrogate(e) => write!(
                f,
                "invalid unicode sequence: lone surrogate found: 0x{:04X} at offset {}",
                e.surrogate, self.offset
            ),
        }
    }
}

impl core::error::Error for UnescapeError {}
impl core::error::Error for DecodeUtf8Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            DecodeUtf8Error::Utf8(e) => Some(e),
            DecodeUtf8Error::Unescape(e) => Some(e),
        }
    }
}

// =============================================================================
// Utilities
// =============================================================================

// A const lookup table for JSON escape sequences.
// Maps a byte to its escaped `&'static str` representation.
// `None` indicates the byte does not need to be escaped.
const ESCAPE_TABLE: [Option<&'static str>; 256] = {
    let mut table: [Option<&'static str>; 256] = [None; 256];

    // Special characters
    table[b'"' as usize] = Some(r#"\""#);
    table[b'\\' as usize] = Some(r#"\\"#);

    // Common control characters with short escapes
    table[0x08] = Some(r#"\b"#); // Backspace
    table[0x09] = Some(r#"\t"#); // Tab
    table[0x0A] = Some(r#"\n"#); // Line Feed
    table[0x0C] = Some(r#"\f"#); // Form Feed
    table[0x0D] = Some(r#"\r"#); // Carriage Return

    // The rest of the control characters must be `\uXXXX` encoded.
    // We can pre-calculate and store all of them as static strings.
    table[0x00] = Some(r#"\u0000"#);
    table[0x01] = Some(r#"\u0001"#);
    table[0x02] = Some(r#"\u0002"#);
    table[0x03] = Some(r#"\u0003"#);
    table[0x04] = Some(r#"\u0004"#);
    table[0x05] = Some(r#"\u0005"#);
    table[0x06] = Some(r#"\u0006"#);
    table[0x07] = Some(r#"\u0007"#);
    // 0x08 to 0x0D are already handled above
    table[0x0B] = Some(r#"\u000b"#);
    table[0x0E] = Some(r#"\u000e"#);
    table[0x0F] = Some(r#"\u000f"#);
    table[0x10] = Some(r#"\u0010"#);
    table[0x11] = Some(r#"\u0011"#);
    table[0x12] = Some(r#"\u0012"#);
    table[0x13] = Some(r#"\u0013"#);
    table[0x14] = Some(r#"\u0014"#);
    table[0x15] = Some(r#"\u0015"#);
    table[0x16] = Some(r#"\u0016"#);
    table[0x17] = Some(r#"\u0017"#);
    table[0x18] = Some(r#"\u0018"#);
    table[0x19] = Some(r#"\u0019"#);
    table[0x1A] = Some(r#"\u001a"#);
    table[0x1B] = Some(r#"\u001b"#);
    table[0x1C] = Some(r#"\u001c"#);
    table[0x1D] = Some(r#"\u001d"#);
    table[0x1E] = Some(r#"\u001e"#);
    table[0x1F] = Some(r#"\u001f"#);

    table
};

// A simple boolean-like lookup table for SIMD.
// 0 = no escape needed, 1 = escape needed.
// This is very compact (256 bytes) and fits easily in the L1 cache.
#[allow(unused)]
const ESCAPE_DECISION_TABLE: [u8; 256] = {
    let mut table = [0u8; 256];
    let mut i = 0;
    while i < 256 {
        if ESCAPE_TABLE[i].is_some() {
            table[i] = 1;
        }
        i += 1;
    }
    table
};

// This is the SIMD version, compiled only when the "simd" feature is enabled on nightly build.
#[cfg(all(feature = "simd", nightly))]
#[inline]
fn find_escape_char(bytes: &[u8]) -> Option<usize> {
    use std::simd::{Simd, prelude::SimdPartialEq, prelude::SimdPartialOrd};

    const LANES: usize = 16; // Process 16 bytes at a time (fits in SSE2/AVX)
    let mut i = 0;

    // SIMD main loop
    while i + LANES <= bytes.len() {
        // Load 16 bytes from the slice into a SIMD vector.
        let chunk = Simd::<u8, LANES>::from_slice(&bytes[i..]);

        // Create comparison vectors. These are effectively 16 copies of the byte.
        let space_v = Simd::splat(b' ' - 1); // For the < ' ' check (i.e., <= 0x1F)
        let quote_v = Simd::splat(b'"');
        let slash_v = Simd::splat(b'\\');

        // Perform all 16 comparisons at once. The result is a mask.
        let lt_space_mask = chunk.simd_le(space_v);
        let eq_quote_mask = chunk.simd_eq(quote_v);
        let eq_slash_mask = chunk.simd_eq(slash_v);

        // Combine the masks. A byte needs escaping if ANY of the conditions are true.
        let combined_mask = lt_space_mask | eq_quote_mask | eq_slash_mask;

        // Check if any lane in the combined mask is true.
        if combined_mask.any() {
            // If yes, find the index of the *first* true lane.
            // trailing_zeros() on the bitmask gives us this index directly.
            let first_match_index = combined_mask.to_bitmask().trailing_zeros() as usize;
            return Some(i + first_match_index);
        }

        i += LANES;
    }

    // Handle the remaining bytes (if any) with the simple iterator method.
    if i < bytes.len() {
        if let Some(pos) = bytes[i..]
            .iter()
            .position(|&b| ESCAPE_DECISION_TABLE[b as usize] != 0)
        {
            return Some(i + pos);
        }
    }

    None
}

#[cfg(all(feature = "simd", not(nightly), target_arch = "x86_64"))]
#[inline]
fn find_escape_char(bytes: &[u8]) -> Option<usize> {
    // This is the stable Rust path using explicit CPU intrinsics.
    // It's guarded by cfg flags to only compile on x86_64 with the simd feature.
    use std::arch::x86_64::*;

    let mut i = 0;
    const LANES: usize = 16; // SSE2 works on 128-bit registers, which is 16 bytes.

    // On x86_64, we can tell the compiler to use SSE2 features in this specific function.
    // This is safe because we've already checked the target architecture.
    #[target_feature(enable = "sse2")]
    unsafe fn find_in_chunk(bytes: &[u8], i: usize) -> Option<usize> {
        // Load 16 bytes of data from the slice.
        let chunk = unsafe { _mm_loadu_si128(bytes.as_ptr().add(i) as *const _) };

        // Create comparison vectors for quote and slash.
        let quote_v = _mm_set1_epi8(b'"' as i8);
        let slash_v = _mm_set1_epi8(b'\\' as i8);

        // Emulate unsigned comparison for control characters
        // Create a vector with the value 0x80 in each lane.
        let bias = _mm_set1_epi8(0x80u8 as i8);
        // Create the comparison vector for bytes < 0x20 (' ').
        let space_v = _mm_set1_epi8(b' ' as i8);

        // Bias both the input chunk and the comparison vector by XORing with 0x80.
        let biased_chunk = _mm_xor_si128(chunk, bias);
        let biased_space_v = _mm_xor_si128(space_v, bias);

        // Now, a signed less-than comparison on the biased values gives the
        // same result as an unsigned less-than on the original values.
        let lt_space_mask = _mm_cmplt_epi8(biased_chunk, biased_space_v);

        // Perform the equality comparisons (these are unaffected by signedness).
        let eq_quote_mask = _mm_cmpeq_epi8(chunk, quote_v);
        let eq_slash_mask = _mm_cmpeq_epi8(chunk, slash_v);

        // Combine the results.
        let combined_mask = _mm_or_si128(lt_space_mask, _mm_or_si128(eq_quote_mask, eq_slash_mask));

        // Create a bitmask to find the first match.
        let mask = _mm_movemask_epi8(combined_mask);

        if mask != 0 {
            Some(i + mask.trailing_zeros() as usize)
        } else {
            None
        }
    }
    // Main loop
    while i + LANES <= bytes.len() {
        if let Some(result) = unsafe { find_in_chunk(bytes, i) } {
            return Some(result);
        }
        i += LANES;
    }

    // Handle the remainder with the fast scalar lookup.
    if i < bytes.len() {
        if let Some(pos) = bytes[i..]
            .iter()
            .position(|&b| ESCAPE_DECISION_TABLE[b as usize] != 0)
        {
            return Some(i + pos);
        }
    }

    None
}

// A fallback for when SIMD feature is off.
#[cfg(not(feature = "simd"))]
#[inline]
fn find_escape_char(bytes: &[u8]) -> Option<usize> {
    bytes
        .iter()
        .position(|&b| ESCAPE_DECISION_TABLE[b as usize] != 0)
}

#[cfg(all(feature = "simd", not(nightly), not(target_arch = "x86_64")))]
compile_error! { "simd requires nightly or target_arch = \"x86_64\"" }

/// Static table mapping every u8 -> a &'static [u8] of length 1.
/// This lets us return a `'static` slice for any single byte cheaply.
const U8_TABLE: [[u8; 1]; 256] = {
    let mut arr = [[0u8; 1]; 256];
    let mut i = 0usize;
    while i < 256 {
        arr[i] = [i as u8];
        i += 1;
    }
    arr
};

#[inline(always)]
fn byte_as_static_slice(b: u8) -> &'static [u8] {
    // coerce from &'static [u8;1] to &'static [u8]
    &U8_TABLE[b as usize]
}

// The following function is copied from the `percent-encoding` crate, version 2.3.2.
// Source: https://github.com/servo/rust-url/blob/22b925f93ad505a830f1089538a9ed6f5fd90612/percent_encoding/src/lib.rs#L337-L365
//
// It is licensed under the same terms as the `percent-encoding` crate (MIT/Apache-2.0).
//
// This helper is used to efficiently convert a Cow<'_, [u8]> to a Cow<'_, str>
// lossily, with a specific optimization to avoid a re-allocation when the input
// is an owned, valid UTF-8 Vec<u8>.
#[cfg(feature = "alloc")]
#[allow(ambiguous_wide_pointer_comparisons)]
fn decode_utf8_lossy(input: Cow<'_, [u8]>) -> Cow<'_, str> {
    // Note: This function is duplicated in `form_urlencoded/src/query_encoding.rs`.
    match input {
        Cow::Borrowed(bytes) => String::from_utf8_lossy(bytes),
        Cow::Owned(bytes) => {
            match String::from_utf8_lossy(&bytes) {
                Cow::Borrowed(utf8) => {
                    // If from_utf8_lossy returns a Cow::Borrowed, then we can
                    // be sure our original bytes were valid UTF-8. This is because
                    // if the bytes were invalid UTF-8 from_utf8_lossy would have
                    // to allocate a new owned string to back the Cow so it could
                    // replace invalid bytes with a placeholder.

                    // First we do a debug_assert to confirm our description above.
                    let raw_utf8: *const [u8] = utf8.as_bytes();
                    debug_assert!(core::ptr::eq(raw_utf8, &*bytes));

                    // Given we know the original input bytes are valid UTF-8,
                    // and we have ownership of those bytes, we re-use them and
                    // return a Cow::Owned here.
                    Cow::Owned(unsafe { String::from_utf8_unchecked(bytes) })
                }
                Cow::Owned(s) => Cow::Owned(s),
            }
        }
    }
}

/// Compare two chunk-iterators by their concatenated byte stream (streaming,
/// zero allocations).
///
/// This is allocation-free: it streams through both iterators, comparing
/// overlapping prefixes and carrying the remainder of the longer chunk
/// forward into the next round.
fn chunks_eq<'a, I1, A, I2, B>(mut a: I1, mut b: I2) -> bool
where
    A: 'a + AsRef<[u8]> + ?Sized,
    B: 'a + AsRef<[u8]> + ?Sized,
    I1: Iterator<Item = &'a A>,
    I2: Iterator<Item = &'a B>,
{
    let mut a_rem: &[u8] = &[];
    let mut b_rem: &[u8] = &[];

    loop {
        // If the remainder buffer for 'a' is empty, try to get the next chunk.
        if a_rem.is_empty() {
            match a.next() {
                Some(chunk) => a_rem = chunk.as_ref(),
                // 'a' is exhausted. They are equal only if 'b' is also exhausted.
                None => return b_rem.is_empty() && b.next().is_none(),
            }
        }

        // If the remainder buffer for 'b' is empty, try to get the next chunk.
        if b_rem.is_empty() {
            match b.next() {
                Some(chunk) => b_rem = chunk.as_ref(),
                // 'b' is exhausted, but we know 'a' is not (since a_rem is non-empty).
                // Therefore, they cannot be equal.
                None => return false,
            }
        }

        // At this point, both a_rem and b_rem are guaranteed to be non-empty.
        // Determine the length of the smaller chunk to compare.
        let n = a_rem.len().min(b_rem.len());

        // Compare the overlapping parts of the chunks.
        if a_rem[..n] != b_rem[..n] {
            return false;
        }

        // Move the slices past the part we just compared.
        a_rem = &a_rem[n..];
        b_rem = &b_rem[n..];
    }
}

#[inline]
fn display_bytes_utf8(bytes: &[u8], f: &mut fmt::Formatter<'_>, lossy: bool) -> fmt::Result {
    for chunk in bytes.utf8_chunks() {
        f.write_str(chunk.valid())?;

        if !chunk.invalid().is_empty() {
            if lossy {
                f.write_char(char::REPLACEMENT_CHARACTER)?
            } else {
                return Err(fmt::Error);
            }
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use core::fmt::Display;
    use std::{io::Read as _, string::ToString as _, vec};

    use super::*;

    // ===================== Escape ===================== //

    fn test_escape_typical(input: &str, want: &str) {
        let got = escape_str(input).collect::<String>();
        assert_eq!(got, want);

        // Test PartialEq too
        assert_eq!(escape_str(input), want);

        // Let's test explicit regardless
        let got = explicit::escape_str(input).collect::<String>();
        assert_eq!(got, want);

        // Test PartialEq too
        assert_eq!(escape_str(input), want)
    }

    #[test]
    fn test_empty_string() {
        test_escape_typical("", "");
    }

    #[test]
    fn test_quotes() {
        test_escape_typical("\"hello\"", "\\\"hello\\\"")
    }

    #[test]
    fn test_backslash() {
        test_escape_typical("\\hello\\", "\\\\hello\\\\");
    }

    #[test]
    fn test_slash() {
        test_escape_typical("/hello/", "/hello/");
    }

    #[test]
    fn test_control_chars() {
        test_escape_typical("\n\r\t\x08\x0C", "\\n\\r\\t\\b\\f");
    }

    #[test]
    fn test_escape_fully() {
        let input = "Hello, \"world\"!\nThis contains a \\ backslash and a \t tab.";
        let expected = r#"Hello, \"world\"!\nThis contains a \\ backslash and a \t tab."#;
        test_escape_typical(input, expected);
    }

    #[test]
    fn test_other_control_chars() {
        let input = "Null:\0, Bell:\x07";
        let expected = r#"Null:\u0000, Bell:\u0007"#;
        test_escape_typical(input, expected);

        test_escape_typical("\x00\x1F", "\\u0000\\u001f");
        test_escape_typical("\x19", "\\u0019");
    }

    #[test]
    fn test_iterator_chunks() {
        let input = "prefix\npostfix";
        let mut iter = escape_str(input);
        assert_eq!(iter.next(), Some("prefix"));
        assert_eq!(iter.next(), Some(r#"\n"#));
        assert_eq!(iter.next(), Some("postfix"));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_no_escape_needed() {
        let input = "A simple string with no escapes.";
        let mut iter = escape_str(input);
        assert_eq!(iter.next(), Some("A simple string with no escapes."));
        assert_eq!(iter.next(), None);

        let input = "café";
        let mut iter = escape_str(input);
        assert_eq!(iter.next(), Some("café"));
        assert_eq!(iter.next(), None);

        let input = "❤️";
        let mut iter = escape_str(input);
        assert_eq!(iter.next(), Some("❤️"));
        assert_eq!(iter.next(), None);
    }

    // ===================== Unescape ===================== //

    #[test]
    fn test_byte_table() {
        assert_eq!(byte_as_static_slice(0), &[0]);
        assert_eq!(byte_as_static_slice(5), &[5]);
        assert_eq!(byte_as_static_slice(255), &[255]);
    }

    fn test_unescape_typical<I: AsRef<[u8]> + ?Sized>(input: &I, want: &str) {
        let got = unescape(input).decode_utf8().unwrap();
        assert_eq!(got, want);

        // Test PartialEq too
        assert_eq!(unescape(input), want);

        // Help display
        assert_display(unescape(input).display_utf8(), Ok(want));

        // Let's test explicit regardless
        let got = explicit::unescape(input).decode_utf8().unwrap();
        assert_eq!(got, want);

        // Test PartialEq too
        assert_eq!(explicit::unescape(input), want);

        // Help display
        assert_display(explicit::unescape(input).display_utf8(), Ok(want));
    }

    #[test]
    fn test_unicode_escape_basic_unescape() {
        // \u4E16 => 世 (E4 B8 96)
        let s = "X\\u4E16Y";
        test_unescape_typical(s, "X世Y");

        let s = "Snow: \\u2603"; // \u2603 => ☃
        test_unescape_typical(s, "Snow: ☃");

        let s = "A \\u03A9 B"; // Ω is U+03A9
        test_unescape_typical(s, "A Ω B");
    }

    #[test]
    fn test_surrogate_pair_unescape() {
        // 😀 is U+1F600 -> in JSON: \uD83D\uDE00
        let s = "A\\uD83D\\uDE00B";
        test_unescape_typical(s, "A😀B")
    }

    #[test]
    fn test_invalid_escape_unescape() {
        let s = b"\\x";
        let mut u = unescape(s);

        match u.next() {
            Some(Err(UnescapeError {
                kind: UnescapeErrorKind::InvalidEscape(InvalidEscapeError { found: b'x' }),
                offset: 1,
            })) => {}
            _ => panic!("expected invalid escape"),
        }

        // Let's test explicit regardless
        let mut u = explicit::unescape(s);

        match u.next() {
            Some(Err(UnescapeError {
                kind: UnescapeErrorKind::InvalidEscape(InvalidEscapeError { found: b'x' }),
                offset: 1,
            })) => {}
            _ => panic!("expected invalid escape"),
        }
    }

    #[test]
    fn test_simple_unescape() {
        let input = "Hello\\nWorld\\\"!"; // "Hello\nWorld\"!"
        test_unescape_typical(input, "Hello\nWorld\"!")
    }

    #[test]
    fn test_truncated_unicode() {
        let input = "Trunc: \\u12"; // too short
        let it = unescape(input);
        let mut found = false;
        for r in it {
            match r {
                Ok(_) => continue,
                Err(UnescapeError {
                    kind: UnescapeErrorKind::UnexpectedEof,
                    offset: 4,
                }) => {
                    found = true;
                    break;
                }
                Err(_) => break,
            }
        }
        assert!(found);

        // Let's test explicit regardless
        assert_eq!(
            explicit::unescape(input).next(),
            Some(Err(UnescapeError {
                kind: UnescapeErrorKind::UnexpectedEof,
                offset: 4,
            }))
        );
    }

    // ===================== Chunk_Eq ===================== //

    #[test]
    fn test_empty_iterators_are_equal() {
        let a: Vec<&[u8]> = vec![];
        let b: Vec<&[u8]> = vec![];
        assert!(chunks_eq(a.into_iter(), b.into_iter()));
    }

    #[test]
    fn test_empty_vs_non_empty() {
        let a: Vec<&[u8]> = vec![];
        let b = vec![&[1, 2, 3]];
        assert!(!chunks_eq(a.into_iter(), b.into_iter()));

        // And the other way around
        let a = vec![&[1, 2, 3]];
        let b: Vec<&[u8]> = vec![];
        assert!(!chunks_eq(a.into_iter(), b.into_iter()));
    }

    #[test]
    fn test_single_identical_chunks() {
        let a = vec!["hello world"];
        let b = vec!["hello world"];
        assert!(chunks_eq(a.into_iter(), b.into_iter()));
    }

    #[test]
    fn test_different_chunk_boundaries_str() {
        // This is the key test: the concatenated content is identical,
        // but the chunk divisions are different.
        let a = vec!["he", "llo", " ", "world"];
        let b = vec!["hello ", "wo", "rld"];
        assert!(chunks_eq(a.into_iter(), b.into_iter()));
    }

    #[test]
    fn test_different_chunk_boundaries_bytes() {
        let a = vec![&[1, 2], &[3, 4, 5][..]];
        let b = vec![&[1, 2, 3], &[4, 5][..]];
        assert!(chunks_eq(a.into_iter(), b.into_iter()));
    }

    #[test]
    fn test_one_long_vs_many_short() {
        let a = vec!["a-long-single-chunk"];
        let b = vec!["a", "-", "long", "-", "single", "-", "chunk"];
        assert!(chunks_eq(a.into_iter(), b.into_iter()));
    }

    #[test]
    fn test_unequal_content_same_length() {
        let a = vec!["hello"];
        let b = vec!["hallo"];
        assert!(!chunks_eq(a.into_iter(), b.into_iter()));
    }

    #[test]
    fn test_unequal_at_chunk_boundary() {
        let a = vec!["ab", "c"]; // "abc"
        let b = vec!["ab", "d"]; // "abd"
        assert!(!chunks_eq(a.into_iter(), b.into_iter()));
    }

    #[test]
    fn test_one_is_prefix_of_other() {
        // a is shorter
        let a = vec!["user", "name"]; // "username"
        let b = vec!["user", "name", "123"]; // "username123"
        assert!(!chunks_eq(a.into_iter(), b.into_iter()));

        // b is shorter
        let a = vec!["user", "name", "123"];
        let b = vec!["user", "name"];
        assert!(!chunks_eq(a.into_iter(), b.into_iter()));
    }

    #[test]
    fn test_complex_remainer_logic() {
        // This tests the carry-over logic extensively.
        // a: [1,2,3], [4,5], [6,7,8,9], [10]
        // b: [1,2], [3,4,5,6], [7,8], [9,10]
        let a = vec![&[1, 2, 3], &[4, 5][..], &[6, 7, 8, 9], &[10]];
        let b = vec![&[1, 2], &[3, 4, 5, 6][..], &[7, 8], &[9, 10]];
        assert!(chunks_eq(a.into_iter(), b.into_iter()));
    }

    #[test]
    fn test_with_vec_references() {
        let v_a1 = vec![1, 2];
        let v_a2 = vec![3, 4, 5];
        let a_data = vec![&v_a1, &v_a2];

        let v_b1 = vec![1, 2, 3];
        let v_b2 = vec![4, 5];
        let b_data = vec![&v_b1, &v_b2];
        assert!(chunks_eq(a_data.into_iter(), b_data.into_iter()));
    }

    // ===================== Unescape Read ===================== //
    #[test]
    fn bytes_provenance() {
        // Input chosen so we hit the "final literal" branch and then try to backtrack.
        let input = b"hello";
        let mut iter = explicit::unescape(input);

        // First call yields the entire "hello" as one literal chunk.
        let chunk = iter.next().unwrap().unwrap();
        assert_eq!(chunk.literal, b"hello");

        // At this point, before the fix, `iter.bytes` would have been set to `&[]`
        // (not tied to `input`), so later pointer arithmetic could underflow.
        // After the fix, `iter.bytes` is `&input[input.len()..]`, which is safe.
        assert!(core::ptr::eq(iter.bytes, &input[input.len()..]));

        // -- ESCAPE --
        let input = "hello";
        let mut iter = explicit::escape_str(input);

        // First call yields the entire "hello" as one literal chunk.
        let chunk = iter.next().unwrap();
        assert_eq!(chunk.literal(), "hello");

        // At this point, before the fix, `iter.bytes` would have been set to `&[]`
        // (not tied to `input`), so later pointer arithmetic could underflow.
        // After the fix, `iter.bytes` is `&input[input.len()..]`, which is safe.
        assert!(core::ptr::eq(
            unsafe { str::from_utf8_unchecked(iter.bytes) },
            &input[input.len()..]
        ));

        // -- ESCAPE --
        let mut iter = escape_str(input);

        // First call yields the entire "hello" as one literal chunk.
        let chunk = iter.next().unwrap();
        assert_eq!(chunk, "hello");

        // At this point, before the fix, `iter.bytes` would have been set to `&[]`
        // (not tied to `input`), so later pointer arithmetic could underflow.
        // After the fix, `iter.bytes` is `&input[input.len()..]`, which is safe.
        assert!(core::ptr::eq(
            unsafe { str::from_utf8_unchecked(iter.bytes) },
            &input[input.len()..]
        ))
    }

    #[test]
    fn test_read_simple() {
        let input = br#"hello world"#;
        let mut reader = unescape(input);
        let mut buf = [0u8; 20];

        let bytes_read = reader.read(&mut buf).unwrap();

        assert_eq!(bytes_read, 11);
        assert_eq!(&buf[..bytes_read], b"hello world");

        // Second read should return 0 (EOF)
        let bytes_read_eof = reader.read(&mut buf).unwrap();
        assert_eq!(bytes_read_eof, 0);
    }

    #[test]
    fn test_read_with_simple_escapes() {
        let input = br#"hello\tworld\nline2"#;
        let mut reader = unescape(input);
        let mut buf = Vec::new();

        reader.read_to_end(&mut buf).unwrap();

        assert_eq!(buf, b"hello\tworld\nline2");
    }

    #[test]
    fn test_read_into_small_buffer_multiple_calls() {
        let input = br#"this is a long string with no escapes"#;
        let mut reader = unescape(input);
        let mut buf = [0u8; 10];
        let mut result = Vec::new();

        loop {
            match reader.read(&mut buf) {
                Ok(0) => break, // EOF
                Ok(n) => {
                    result.extend_from_slice(&buf[..n]);
                }
                Err(e) => panic!("Read error: {}", e),
            }
        }

        assert_eq!(result, input);
    }

    #[test]
    fn test_read_multibyte_char_across_buffer_boundary() {
        // The grinning face emoji 😀 is \uD83D\uDE00, which is 4 bytes in UTF-8: 0xF0 0x9F 0x98 0x80
        let input = br#"emoji: \uD83D\uDE00 is here"#;
        let mut reader = unescape(input);

        // Buffer is small, forcing the 4-byte emoji to be written across multiple calls
        let mut buf = [0u8; 8];
        let mut result = Vec::new();

        // First read: "emoji: " (7 bytes) + first byte of emoji
        let n1 = reader.read(&mut buf).unwrap();
        assert_eq!(n1, 8);
        assert_eq!(&buf[..n1], b"emoji: \xF0");
        result.extend_from_slice(&buf[..n1]);

        // Second read: next 3 bytes of emoji + " is h"
        let n2 = reader.read(&mut buf).unwrap();
        assert_eq!(n2, 8);
        assert_eq!(&buf[..n2], b"\x9F\x98\x80 is h");
        result.extend_from_slice(&buf[..n2]);

        // Third read: "ere"
        let n3 = reader.read(&mut buf).unwrap();
        assert_eq!(n3, 3);
        assert_eq!(&buf[..n3], b"ere");
        result.extend_from_slice(&buf[..n3]);

        // Final read should be EOF
        let n4 = reader.read(&mut buf).unwrap();
        assert_eq!(n4, 0);

        assert_eq!(result, b"emoji: \xF0\x9F\x98\x80 is here");
        assert_eq!(result, "emoji: 😀 is here".as_bytes());
    }

    #[test]
    fn test_read_error_invalid_escape() {
        let input = br#"hello \q world"#;
        let mut reader = unescape(input);
        let mut buf = [0u8; 20];

        let result = reader.read(&mut buf);

        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
        assert!(err.to_string().contains("invalid escape"));
    }

    #[test]
    fn test_read_error_lone_surrogate() {
        let input = br#"\uD83D rest of data seen"#; // High surrogate without a following low one
        let mut reader = unescape(input);
        let mut buf = [0u8; 10];

        let err = reader.read(&mut buf).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::InvalidData);
        assert!(err.to_string().contains("lone surrogate"));
    }

    #[test]
    fn test_read_empty_input() {
        let input = b"";
        let mut reader = unescape(input);
        let mut buf = [0u8; 10];
        let bytes_read = reader.read(&mut buf).unwrap();
        assert_eq!(bytes_read, 0);
    }

    #[test]
    fn test_read_into_empty_buffer() {
        let input = b"hello";
        let mut reader = unescape(input);
        let mut buf = [0u8; 0];
        let bytes_read = reader.read(&mut buf).unwrap();
        // A read into an empty buffer should always succeed and return 0.
        assert_eq!(bytes_read, 0);
    }

    #[test]
    fn test_read_to_end_optimized() {
        let input = br#"first\nsecond\tthird \uD83D\uDE00 last"#;
        let mut reader = unescape(input);
        let mut buf = Vec::new();

        let bytes_read = reader.read_to_end(&mut buf).unwrap();
        let expected = b"first\nsecond\tthird \xF0\x9F\x98\x80 last";

        assert_eq!(bytes_read, expected.len());
        assert_eq!(buf, expected);
    }

    // ===================== Unescape Display ===================== //

    fn assert_display(display: impl Display, want: Result<&str, ()>) {
        let mut w = String::new();
        let res = fmt::write(&mut w, format_args!("{display}"));

        match want {
            Ok(want) => {
                assert!(res.is_ok());
                assert_eq!(w, want)
            }
            Err(_) => assert!(
                res.is_err(),
                "strict mode should return Err on invalid bytes"
            ),
        }
    }

    // -- NON-LOSSY TESTS (must be perfect) --

    #[test]
    fn test_display_simple_string() {
        let display = unescape("hello world").display_utf8();
        assert_display(display, Ok("hello world"));
    }

    #[test]
    fn test_display_empty_string() {
        assert_display(unescape("").display_utf8(), Ok(""));
    }

    #[test]
    fn test_display_standard_escapes() {
        let input = br#"\" \\ \/ \b \f \n \r \t"#;
        let expected = "\" \\ / \x08 \x0C \n \r \t";
        assert_display(unescape(input).display_utf8(), Ok(expected));
    }

    #[test]
    fn test_display_non_escaped_utf8() {
        let input = "你好, world".as_bytes();
        let expected = "你好, world";
        assert_display(unescape(input).display_utf8(), Ok(expected));
    }

    #[test]
    fn test_display_unicode_escape_bmp() {
        // cent sign: \u00A2 -> C2 A2 (2 bytes)
        let input = br"a\u00A2b";
        let expected = "a¢b";
        assert_display(unescape(input).display_utf8(), Ok(expected));
    }

    #[test]
    fn test_display_mixed_content() {
        let input = br#"Text with \n, \u00A2, and \uD83D\uDE0E emojis."#;
        let expected = "Text with \n, ¢, and 😎 emojis.";
        assert_display(unescape(input).display_utf8(), Ok(expected));
    }

    #[test]
    fn test_display_starts_and_ends_with_escape() {
        let input = br#"\u00A2hello\t"#;
        let expected = "¢hello\t";
        assert_display(unescape(input).display_utf8(), Ok(expected));
    }

    // -- NON-LOSSY ERROR TESTS --

    #[test]
    fn test_display_err_invalid_escape() {
        assert_display(unescape(br"hello \z world").display_utf8(), Err(()));
    }

    #[test]
    fn test_display_err_incomplete_unicode() {
        assert_display(unescape(br"\u123").display_utf8(), Err(()));
    }

    #[test]
    fn test_display_err_invalid_hex_in_unicode() {
        assert_display(unescape(br"\u123g").display_utf8(), Err(()));
    }

    #[test]
    fn test_display_err_lone_high_surrogate() {
        assert_display(unescape(br"\uD800").display_utf8(), Err(()));
    }

    #[test]
    fn test_display_err_high_surrogate_not_followed_by_low() {
        assert_display(unescape(br"\uD800\uABCD").display_utf8(), Err(()));
    }

    #[test]
    fn test_display_err_invalid_source_utf8() {
        // A valid UTF-8 sequence for 'h' followed by an invalid byte
        assert_display(unescape(b"h\x80ello").display_utf8(), Err(()));
    }

    #[test]
    fn strict_valid_multi_byte_split() {
        // "€" U+20AC => bytes [0xE2, 0x82, 0xAC]
        let input = &[0xE2, 0x82, 0xAC];
        let display = unescape(input).display_utf8();
        assert_display(display, Ok("€"));
    }

    #[test]
    fn strict_errors_on_invalid_start_byte() {
        let input = &[0xFF, b'a'];
        let display = unescape(input).display_utf8();

        assert_display(display, Err(()));
    }

    // -- LOSSY TESTS --

    #[test]
    fn lossy_replaces_invalid_start_byte() {
        // 0xFF is invalid as a leading UTF-8 byte.
        let input = &[0xFF, b'a']; // invalid byte then ASCII 'a';
        let display = unescape(input).display_utf8_lossy();
        // replacement char + 'a'
        assert_display(display, Ok("\u{FFFD}a"));
    }

    #[test]
    fn lossy_handles_trailing_incomplete_bytes() {
        // A trailing incomplete 3-byte sequence: [0xE2, 0x82] (missing 0xAC)
        let input: &[u8] = &[0xE2, 0x82];
        let display = unescape(input).display_utf8_lossy();
        // Should replace incomplete tail with U+FFFD.
        assert_display(display, Ok("\u{FFFD}"));
    }

    #[test]
    fn test_display_lossy_invalid_source_utf8() {
        // The invalid byte sequence should be replaced.
        let input = b"valid\xF0\x90\x80invalid";
        let expected = "valid\u{FFFD}invalid";
        assert_display(unescape(input).display_utf8_lossy(), Ok(expected));
    }

    #[test]
    fn test_display_lossy_invalid_escape_truncates() {
        // In lossy mode, an invalid JSON escape stops the processing.
        let input = br"this is ok \n but this is not \z";
        let expected = "this is ok \n";
        assert_display(unescape(input).display_utf8_lossy(), Ok(expected));
    }

    #[test]
    fn test_display_lossy_incomplete_unicode_truncates() {
        let input = br"truncate after \n \uD83D";
        let expected = "truncate after \n";
        assert_display(unescape(input).display_utf8_lossy(), Ok(expected));
    }

    // Inspired by and copied from memchr
    #[test]
    fn sync_regression() {
        use core::panic::{RefUnwindSafe, UnwindSafe};

        fn assert_send_sync<T: Send + Sync + UnwindSafe + RefUnwindSafe>() {}
        assert_send_sync::<Unescape<'_>>();
        assert_send_sync::<Escape<'_>>();
    }
}

#[cfg(test)]
mod find_escape_char_tests {
    use std::format;

    use super::{ESCAPE_DECISION_TABLE, find_escape_char};

    /// Helper function to run a single test case and provide a clear error message on failure.
    fn run_test(input: &str, expected: Option<usize>, case_name: &str) {
        let result = find_escape_char(input.as_bytes());
        assert_eq!(result, expected, "Failed test case: '{}'", case_name);
    }

    #[test]
    fn test_no_escapes() {
        run_test("", None, "Empty string");
        run_test("Hello, world!", None, "Simple ASCII");
        run_test("This string is exactly 16 bytes", None, "16-byte ASCII");
        run_test(
            "This string is over 16 bytes long now",
            None,
            "Over 16-byte ASCII",
        );

        // The original source of the bug: non-ASCII UTF-8 characters.
        // This ensures the signedness bug is truly fixed.
        run_test("Hello, éàçüö!", None, "Non-ASCII UTF-8");
        run_test("Testing with emojis 😀❤️✅", None, "Emojis");
    }

    #[test]
    fn test_single_escapes() {
        run_test("\"", Some(0), "Quote at start");
        run_test("Hello \" world", Some(6), "Quote in middle");
        run_test("Hello\\", Some(5), "Backslash at end");
        run_test("\n", Some(0), "Control char (newline) at start");
        run_test("Hello\tworld", Some(5), "Control char (tab) in middle");
        run_test(
            "Control char at end\u{08}",
            Some(19),
            "Control char (backspace) at end",
        );
    }

    #[test]
    fn test_finds_first_of_multiple() {
        // This confirms it always finds the *first* match, not a later one.
        run_test("a\"b\\c\nd", Some(1), "Finds first quote");
        run_test("ab\\c\"d\ne", Some(2), "Finds first backslash");
        run_test("abc\nd\"e\\f", Some(3), "Finds first control char");
        run_test("\"\n\\", Some(0), "Multiple escapes at start");
    }

    #[test]
    fn test_simd_chunk_boundaries() {
        // These tests are critical for verifying the SIMD logic. A chunk is 16 bytes.
        let s15 = "a".repeat(15);
        let s16 = "a".repeat(16);
        let s17 = "a".repeat(17);

        // Escape at the exact end of the first 16-byte chunk
        run_test(&format!("{}\"", s15), Some(15), "Escape at index 15");

        // Escape at the exact start of the second 16-byte chunk
        run_test(&format!("{}\n", s16), Some(16), "Escape at index 16");

        // Escape within the second chunk
        run_test(&format!("{}\t", s17), Some(17), "Escape at index 17");

        // A long string with an escape several chunks in
        let long = "a".repeat(40);
        run_test(
            &format!("{}\\\\", long),
            Some(40),
            "Escape deep in a long string",
        );
    }

    #[test]
    fn test_remainder_logic() {
        // These tests ensure the scalar fallback logic works correctly for inputs
        // that are not a multiple of 16 bytes long.

        // String shorter than 16 bytes
        run_test("short\nstring", Some(5), "Short string with escape");
        run_test("no escapes", None, "Short string no escape");

        // String with 17 bytes (16 for SIMD, 1 for remainder)
        let s16 = "a".repeat(16);
        run_test(
            &format!("{}\"", s16),
            Some(16),
            "Escape in 1-byte remainder",
        );

        // String with 31 bytes (16 for SIMD, 15 for remainder)
        let s15 = "b".repeat(15);
        run_test(
            &format!("{}{}\t", s15, s15),
            Some(30),
            "Escape at end of 15-byte remainder",
        );
    }

    #[test]
    fn test_all_escapable_bytes_individually() {
        // This is the ultimate test. It iterates through all 256 possible byte values
        // and confirms that our function's decision matches the ESCAPE_DECISION_TABLE.
        let prefix = "0123456789abcdef"; // A 16-byte safe prefix to engage the SIMD loop.

        for byte_val in 0..=255u8 {
            // We can't create a &str from invalid UTF-8, so we work with byte slices.
            let mut test_bytes = prefix.as_bytes().to_vec();
            test_bytes.push(byte_val);

            let result = find_escape_char(&test_bytes);
            let expected_to_escape = ESCAPE_DECISION_TABLE[byte_val as usize] == 1;

            if expected_to_escape {
                // If this byte SHOULD be escaped, we expect to find it at index 16.
                assert_eq!(
                    result,
                    Some(16),
                    "Failed to find required escape for byte 0x{:02X}",
                    byte_val
                );
            } else {
                // If this byte should NOT be escaped, we expect to find nothing.
                assert_eq!(
                    result, None,
                    "Incorrectly found an escape for byte 0x{:02X}",
                    byte_val
                );
            }
        }
    }
}
