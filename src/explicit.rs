//! More explicit and fine-grained iterators for JSON escaping and unescaping.
//!
//! This module provides an alternative API to the one in the crate root. While the
//! root API yields slices (`&str` or `&[u8]`) that represent the final output,
//! this module's iterators yield "chunk" structs. These structs distinguish between
//! parts of the input that were processed literally and the specific characters
//! that were escaped or unescaped.
//!
//! This approach offers several advantages:
//! - **Greater Control**: You can inspect each component of the transformation,
//!   which can be useful for debugging, logging, or more complex data processing.
//! - **Potential Performance**: By avoiding the need to look up single-byte escape
//!   sequences in a table on every iteration, some workflows may see a minor
//!   performance improvement.
//! - **Clarity**: The structure of the output more closely reflects the transformation
//!   process, which can make the logic easier to follow.
//!
//! # Example: Escaping
//!
//! ```
//! use json_escape::explicit::escape_str;
//!
//! let mut escaper = escape_str("a\nb");
//!
//! // The first chunk contains the literal "a" and the escaped newline.
//! let chunk1 = escaper.next().unwrap();
//! assert_eq!("a", chunk1.literal());
//! assert_eq!(Some(r#"\n"#), chunk1.escaped());
//!
//! // The second chunk contains the literal "b" and no escaped sequence.
//! let chunk2 = escaper.next().unwrap();
//! assert_eq!("b", chunk2.literal());
//! assert_eq!(None, chunk2.escaped());
//!
//! // The iterator is now exhausted.
//! assert!(escaper.next().is_none());
//! ```
//!
//! # Example: Unescaping
//!
//! ```
//! use json_escape::explicit::unescape;
//!
//! let mut unescaper = unescape(br"hello\tworld");
//!
//! // The first chunk contains the literal "hello" and the unescaped tab.
//! let chunk1 = unescaper.next().unwrap().unwrap();
//! assert_eq!(b"hello", chunk1.literal());
//! assert_eq!(Some('\t'), chunk1.unescaped());
//!
//! // The second chunk contains the literal "world" and no unescaped character.
//! let chunk2 = unescaper.next().unwrap().unwrap();
//! assert_eq!(b"world", chunk2.literal());
//! assert_eq!(None, chunk2.unescaped());
//!
//! // The iterator is now exhausted.
//! assert!(unescaper.next().is_none());
//! ```
//!
//! Both `Escape` and `Unescape` iterators provide `display` helpers for easy integration
//! with Rust's formatting system, preserving the zero-allocation benefits of the main API.

#[cfg(feature = "alloc")]
use crate::DecodeUtf8Error;
use crate::{ESCAPE_TABLE, InvalidHexError, LoneSurrogateError, UnescapeError, display_bytes_utf8};
use crate::{InvalidEscapeError, UnescapeErrorKind, find_escape_char};
use core::fmt;
use core::iter::FusedIterator;
use core::str;

#[cfg(feature = "alloc")]
use alloc::{borrow::Cow, string::String, vec::Vec};

//==============================================================================
// Escaping
//==============================================================================

/// Creates an iterator that yields chunks of an escaped JSON string.
///
/// See the [module-level documentation](self) for more details.
#[inline]
pub fn escape_str(s: &str) -> Escape<'_> {
    Escape {
        bytes: s.as_bytes(),
    }
}

/// A chunk of a JSON-escaped string, separating the literal part from the escaped sequence.
///
/// This struct is yielded by the [`Escape`] iterator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EscapedChunk<'a> {
    /// A slice of the original input that did not require escaping.
    literal: &'a str,
    /// The escaped sequence (e.g., `r#"\n"#`, `r#"\""#`) that immediately follows the literal part.
    /// Is `None` if this is the last chunk and it has no trailing escape.
    escaped: Option<&'static str>,
}

impl<'a> EscapedChunk<'a> {
    /// Returns the literal part of the chunk, which is a slice of the original string.
    #[inline]
    pub const fn literal(&self) -> &'a str {
        self.literal
    }

    /// Returns the escaped part of the chunk, if any.
    #[inline]
    pub const fn escaped(&self) -> Option<&'static str> {
        self.escaped
    }
}

impl<'a> fmt::Display for EscapedChunk<'a> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.literal)?;
        if let Some(s) = self.escaped {
            f.write_str(s)?;
        }
        Ok(())
    }
}

/// An iterator over a string that yields [`EscapedChunk`]s.
///
/// Created by the [`escape_str`] function.
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Escape<'a> {
    pub(crate) bytes: &'a [u8],
}

impl<'a> Iterator for Escape<'a> {
    type Item = EscapedChunk<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bytes.is_empty() {
            return None;
        }

        let pos = find_escape_char(self.bytes).unwrap_or(self.bytes.len());
        let (literal_bytes, rest) = self.bytes.split_at(pos);

        // SAFETY: `find_escape_char` guarantees `pos` is on a UTF-8 boundary.
        let literal = unsafe { str::from_utf8_unchecked(literal_bytes) };

        if rest.is_empty() {
            self.bytes = &self.bytes[self.bytes.len()..];
            Some(EscapedChunk {
                literal,
                escaped: None,
            })
        } else {
            let escaped_char_byte = rest[0];
            self.bytes = &rest[1..];
            Some(EscapedChunk {
                literal,
                escaped: Some(
                    ESCAPE_TABLE[escaped_char_byte as usize]
                        .expect("find_escape_char found a byte not in ESCAPE_TABLE"),
                ),
            })
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.bytes.is_empty() {
            (0, Some(0))
        } else {
            // We'll yield at least 1 chunk, and at most `len` chunks if every byte is escaped.
            (1, Some(self.bytes.len()))
        }
    }
}

impl<'a> FusedIterator for Escape<'a> {}

impl<'a> fmt::Display for Escape<'a> {
    /// This allows the escaped output to be written directly to a formatter
    /// without intermediate allocation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for chunk in self.clone() {
            write!(f, "{chunk}")?;
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
    /// This is a convenience for testing, allowing you to check the fully
    /// concatenated result of an `Escape` iterator against a known `&str` or `&[u8]`.
    fn eq(&self, other: &B) -> bool {
        let mut other = other.as_ref();
        for chunk in self.clone() {
            // Check literal part
            if !other.starts_with(chunk.literal.as_bytes()) {
                return false;
            }
            other = &other[chunk.literal.len()..];

            // Check escaped part
            if let Some(escaped_str) = chunk.escaped {
                if !other.starts_with(escaped_str.as_bytes()) {
                    return false;
                }
                other = &other[escaped_str.len()..];
            }
        }
        other.is_empty()
    }
}

impl<'a, 'b> PartialEq<Escape<'a>> for Escape<'b> {
    /// Compares two `Escape` iterators for equality.
    ///
    /// Two `Escape` iterators are considered equal if they'll produce the same **output**.
    /// It first performs a fast check on the underlying byte slices.
    fn eq(&self, other: &Escape<'a>) -> bool {
        // The crate parallel is easier
        crate::Escape { bytes: self.bytes } == crate::Escape { bytes: other.bytes }
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
    fn from(mut iter: Escape<'a>) -> Self {
        match iter.next() {
            None => Cow::Borrowed(""),
            Some(first) => {
                if first.escaped.is_none() {
                    // No escape in the first (and only) chunk, so no escaping was needed.
                    Cow::Borrowed(first.literal)
                } else {
                    // Escaping occurred. We must allocate.
                    let mut s = String::with_capacity(iter.bytes.len() + 16);
                    s.push_str(first.literal);
                    s.push_str(first.escaped.unwrap());
                    s.extend(iter);
                    Cow::Owned(s)
                }
            }
        }
    }
}

//==============================================================================
// Unescaping
//==============================================================================

/// Creates an iterator that yields chunks of an unescaped JSON string.
///
/// See the [module-level documentation](self) for more details.
#[inline]
pub fn unescape<I: AsRef<[u8]> + ?Sized>(input: &I) -> Unescape<'_> {
    Unescape {
        bytes: input.as_ref(),
    }
}

/// Creates a streaming JSON string unescaper that handles enclosing quotes.
///
/// This function is a convenience wrapper around [`unescape`]. If the input byte
/// slice starts and ends with a double-quote (`"`), the quotes are trimmed
/// before the content is unescaped.
///
/// If the input is not enclosed in quotes, this function behaves identically to
/// [`unescape`].
///
/// # Examples
///
/// ```
/// use json_escape::explicit::unescape_quoted;
///
/// // An input string with quotes and an escaped tab.
/// let bytes = br#""\tline""#;
/// let mut unescaper = unescape_quoted(bytes);
///
/// // The first chunk is the unescaped tab character.
/// let chunk1 = unescaper.next().unwrap().unwrap();
/// assert_eq!(b"", chunk1.literal());
/// assert_eq!(Some('\t'), chunk1.unescaped());
///
/// // The second chunk is the literal "line".
/// let chunk2 = unescaper.next().unwrap().unwrap();
/// assert_eq!(b"line", chunk2.literal());
/// assert_eq!(None, chunk2.unescaped());
///
/// // The iterator is now exhausted.
/// assert!(unescaper.next().is_none());
/// ```
#[inline]
pub fn unescape_quoted(bytes: &[u8]) -> Unescape<'_> {
    let inner = if bytes.len() >= 2 && bytes.first() == Some(&b'"') && bytes.last() == Some(&b'"') {
        &bytes[1..bytes.len() - 1]
    } else {
        bytes
    };
    unescape(inner)
}

/// A chunk of a JSON-unescaped byte slice, separating the literal part from the unescaped character.
///
/// This struct is yielded by the [`Unescape`] iterator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnescapedChunk<'a> {
    /// A slice of the original input that did not require unescaping.
    pub(crate) literal: &'a [u8],
    /// The single character that was unescaped.
    /// Is `None` if this is the last chunk and it has no trailing unescaped character.
    pub(crate) unescaped: Option<char>,
}

impl<'a> UnescapedChunk<'a> {
    /// Returns the literal part of the chunk, which is a slice of the original bytes.
    #[inline]
    pub const fn literal(&self) -> &'a [u8] {
        self.literal
    }

    /// Returns the unescaped character, if any.
    #[inline]
    pub const fn unescaped(&self) -> Option<char> {
        self.unescaped
    }

    /// Returns a displayable wrapper that will format the chunk as a UTF-8 string.
    ///
    /// If the literal part of the chunk contains invalid UTF-8 sequences, this
    /// will result in a `fmt::Error`.
    pub fn display_utf8(&self) -> DisplayUnescapedChunk<'_> {
        DisplayUnescapedChunk {
            chunk: self,
            lossy: false,
        }
    }

    /// Returns a displayable wrapper that will format the chunk as a lossy UTF-8 string.
    ///
    /// Any invalid UTF-8 sequences in the literal part of the chunk will be
    /// replaced with the U+FFFD replacement character.
    pub fn display_utf8_lossy(&self) -> DisplayUnescapedChunk<'_> {
        DisplayUnescapedChunk {
            chunk: self,
            lossy: true,
        }
    }
}

/// Helper struct for safely displaying an [`UnescapedChunk`].
pub struct DisplayUnescapedChunk<'a> {
    chunk: &'a UnescapedChunk<'a>,
    lossy: bool,
}

impl<'a> fmt::Display for DisplayUnescapedChunk<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display_bytes_utf8(self.chunk.literal, f, self.lossy)?;
        if let Some(c) = self.chunk.unescaped {
            use fmt::Write as _;

            f.write_char(c)?;
        }
        Ok(())
    }
}

/// An iterator over a byte slice that yields [`UnescapedChunk`]s.
///
/// Created by the [`unescape`] function.
#[derive(Clone)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Unescape<'a> {
    pub(crate) bytes: &'a [u8],
}

impl<'a> Iterator for Unescape<'a> {
    type Item = Result<UnescapedChunk<'a>, UnescapeError>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        use memchr::memchr;

        if self.bytes.is_empty() {
            return None;
        }

        let pos = match memchr(b'\\', self.bytes) {
            Some(p) => p,
            None => {
                // No more backslashes, yield the rest as a final literal chunk.
                let chunk = UnescapedChunk {
                    literal: self.bytes,
                    unescaped: None,
                };
                self.bytes = &self.bytes[self.bytes.len()..]; // fix: totalk
                return Some(Ok(chunk));
            }
        };

        let (literal, rest) = self.bytes.split_at(pos);
        // rest starts with '\\'
        let mut remainder = &rest[1..];

        let unescaped_char = match remainder.first() {
            Some(b'u') => {
                // Temporarily advance past 'u'
                remainder = &remainder[1..];
                // Use a helper from the main unescaper, giving it a mutable slice reference
                // that it can advance.
                match Self::handle_unicode_escape(&mut remainder) {
                    Ok(c) => c,
                    Err(e) => {
                        // FIX: handle_unicode_escape_from_slice already handles this for us.
                        // Adjust offset: error is relative to `\u`, but we need it relative to chunk start.
                        return Some(Err(e));
                    }
                }
            }
            Some(&byte) => {
                remainder = &remainder[1..];
                match UNESCAPE_TABLE[byte as usize] {
                    Some(c) => c,
                    None => {
                        return Some(Err(UnescapeError {
                            kind: UnescapeErrorKind::InvalidEscape(InvalidEscapeError {
                                found: byte,
                            }),
                            // The invalid character is 1 byte after '\'.
                            offset: 1,
                        }));
                    }
                }
            }
            None => {
                return Some(Err(UnescapeError {
                    kind: UnescapeErrorKind::UnexpectedEof,
                    // EOF occurred 1 byte after '\'.
                    offset: 1,
                }));
            }
        };

        self.bytes = remainder;
        Some(Ok(UnescapedChunk {
            literal,
            unescaped: Some(unescaped_char),
        }))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.bytes.is_empty() {
            (0, Some(0))
        } else {
            // Worst-case is \uXXXX -> 1 byte, so 6 -> 1.
            (
                self.bytes.len().saturating_add(1) / 6,
                Some(self.bytes.len()),
            )
        }
    }
}

impl<'a> FusedIterator for Unescape<'a> {}

impl<'a> Unescape<'a> {
    /// Decodes the unescaped byte stream into a UTF-8 string.
    ///
    /// This method consumes the iterator and collects all resulting byte chunks
    /// into a `Cow<[u8]>`, which is then validated as UTF-8. If an unescaping
    /// error occurs, it's returned immediately. If the final sequence of bytes
    /// is not valid UTF-8, a UTF-8 error is returned.
    ///
    /// This is optimized to return a `Cow::Borrowed` if no escapes were present
    /// in the input, avoiding allocation.
    ///
    /// **Requires the `alloc` feature.**
    ///
    /// # Example
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// use json_escape::explicit::unescape;
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
    /// with the replacement character (`U+FFFD`) instead of returning an error.
    ///
    /// An `UnescapeError` can still be returned if the JSON escaping itself is invalid.
    ///
    /// **Requires the `alloc` feature.**
    #[cfg(feature = "alloc")]
    pub fn decode_utf8_lossy(self) -> Result<Cow<'a, str>, UnescapeError> {
        use crate::decode_utf8_lossy;

        Ok(decode_utf8_lossy(self.try_into()?))
    }

    /// Returns a wrapper that implements [`fmt::Display`].
    ///
    /// If an unescaping error or invalid UTF-8 sequence is encountered,
    /// a `fmt::Error` is returned, which will cause `format!` and friends to panic.
    pub fn display_utf8(self) -> DisplayUnescape<'a> {
        DisplayUnescape {
            inner: self,
            lossy: false,
        }
    }

    /// Returns a wrapper that implements [`fmt::Display` for lossy UTF-8 decoding.
    ///
    /// Invalid UTF-8 sequences will be replaced with the replacement character.
    /// An unescaping error will still result in a `fmt::Error`.
    pub fn display_utf8_lossy(self) -> DisplayUnescape<'a> {
        DisplayUnescape {
            inner: self,
            lossy: true,
        }
    }

    /// Parses a unicode escape sequence `\uXXXX` which may be a surrogate pair.
    /// The input slice `bytes` must be positioned *after* the `\u`.
    ///
    /// On success, returns the parsed `char` and advances the slice.
    /// On error, returns an `Err` and the input slice is not modified.
    #[inline(always)]
    fn handle_unicode_escape(bytes: &mut &'a [u8]) -> Result<char, UnescapeError> {
        // Parse first 4 hex digits (\uXXXX)
        //
        // The slice starts *after* '\u'. The first hex digit is at offset 2 from '\'.
        let first = Self::parse_hex4(&bytes, 2)?;

        // High surrogate → must be followed by another \uXXXX low surrogate
        if (0xD800..=0xDBFF).contains(&first) {
            let remaining = &bytes[4..];

            const N: usize = b"\\u".len();

            // EOF before even seeing '\' or 'u' → UnexpectedEof
            if remaining.len() < N {
                return Err(UnescapeError {
                    kind: UnescapeErrorKind::UnexpectedEof,
                    offset: 6,
                });
            }

            // Check for a following `\u` and enough bytes for the second hex sequence.
            if b"\\u" == &remaining[..N] {
                // Try parsing the low surrogate. The slice is advanced by 2 for the `\u`.
                // The first hex digit of the second escape is at offset 8.
                // (\uXXXX\u -> 8 chars from the initial '\')
                match Self::parse_hex4(&remaining[2..], 8) {
                    Ok(low) if (0xDC00..=0xDFFF).contains(&low) => {
                        // We found a valid low surrogate. Combine them.
                        let high_t = first as u32;
                        let low_t = low as u32;
                        let code = 0x10000 + (((high_t - 0xD800) << 10) | (low_t - 0xDC00));
                        let result_char = char::from_u32(code)
                            .expect("valid surrogate pair math should always produce a valid char");

                        // SUCCESS: Advance the original slice past the entire surrogate pair (\uXXXX\uXXXX).
                        *bytes = &remaining[6..]; // Consumes 4 + 2 + 4 = 10 bytes total from the original slice
                        return Ok(result_char);
                    }
                    Ok(_) => {
                        // Got a full escape but not a low surrogate → Lone surrogate
                        return Err(UnescapeError {
                            kind: UnescapeErrorKind::LoneSurrogate(LoneSurrogateError {
                                surrogate: first,
                            }),
                            offset: 6,
                        });
                    }
                    Err(err) => {
                        // parse_hex4 failed for the second part.
                        return Err(err);
                    }
                }
            } else {
                if remaining.len() < 2 {}

                // High surrogate was not followed by a `\u` sequence.
                return Err(UnescapeError {
                    kind: UnescapeErrorKind::LoneSurrogate(LoneSurrogateError { surrogate: first }),
                    // The error is detected after consuming `\uXXXX` (6 bytes total from '\').
                    offset: 6,
                });
            }
        }

        // Not a surrogate → normal path
        match char::from_u32(first as u32) {
            Some(c) => {
                // SUCCESS: Advance the original slice past the 4 hex digits.
                *bytes = &bytes[4..];
                Ok(c)
            }
            None => Err(UnescapeError {
                // The parsed value is not a valid char (e.g., a lone low surrogate).
                kind: UnescapeErrorKind::LoneSurrogate(LoneSurrogateError { surrogate: first }),
                // The error is detected after consuming `\uXXXX` (6 bytes total from '\').
                offset: 6,
            }),
        }
    }

    /// Parses 4 hex digits, optimized for the success path.
    #[inline(always)]
    fn parse_hex4(slice: &[u8], base_offset: u8) -> Result<u16, UnescapeError> {
        // --- HOT PATH ---
        // This is the path we expect to take most of the time.
        if let Some(chunk) = slice.get(..4) {
            // By slicing to 4, we've performed a single bounds check.
            // The compiler now knows any access from chunk[0] to chunk[3] is safe,
            // so it will not generate additional bounds checks.

            // We can now safely access the bytes.
            let b0 = chunk[0];
            let b1 = chunk[1];
            let b2 = chunk[2];
            let b3 = chunk[3];

            // Use the LUT to get the values.
            if let (Some(v0), Some(v1), Some(v2), Some(v3)) = (
                HEX[b0 as usize],
                HEX[b1 as usize],
                HEX[b2 as usize],
                HEX[b3 as usize],
            ) {
                // All characters are valid hex, combine and return.
                let result = (v0 as u16) << 12 | (v1 as u16) << 8 | (v2 as u16) << 4 | (v3 as u16);
                return Ok(result);
            }

            // If we're here, it means the slice was long enough, but one
            // of the characters was not a valid hex digit. Fall through to the cold path
            // to correctly identify which character was invalid.
        }

        // --- COLD PATH ---
        // This path handles all errors. It's marked as `#[cold]` to hint to the
        // compiler that it's less frequently executed.
        #[cold]
        fn handle_error(slice: &[u8], base_offset: u8) -> UnescapeError {
            // Loop through the bytes we *do* have.
            for i in 0..slice.len() {
                let b = slice[i]; // Safe, since i is bounded by slice.len()
                if HEX[b as usize].is_none() {
                    // We found an invalid hex character before running out of bytes.
                    return UnescapeError {
                        kind: UnescapeErrorKind::InvalidHex(InvalidHexError { found: b }),
                        offset: base_offset + i as u8,
                    };
                }
            }

            // If the loop completes, all available characters were valid,
            // but there weren't enough of them.
            UnescapeError {
                kind: UnescapeErrorKind::UnexpectedEof,
                // The error is at the position of the first *missing* character.
                offset: base_offset + slice.len() as u8,
            }
        }

        Err(handle_error(slice, base_offset))
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
    /// Returns `true` if the iterator successfully unescapes to produce a byte
    /// sequence identical to `other`. If an error occurs, returns `false`.
    fn eq(&self, other: &B) -> bool {
        let mut other = other.as_ref();
        let mut char_buf = [0u8; 4];

        for result in self.clone() {
            match result {
                Ok(chunk) => {
                    // Check literal part
                    if !other.starts_with(chunk.literal) {
                        return false;
                    }
                    other = &other[chunk.literal.len()..];

                    // Check unescaped part
                    if let Some(c) = chunk.unescaped {
                        let char_bytes = c.encode_utf8(&mut char_buf);
                        if !other.starts_with(char_bytes.as_bytes()) {
                            return false;
                        }
                        other = &other[char_bytes.len()..];
                    }
                }
                Err(_) => return false, // An erroring iterator cannot be equal.
            }
        }
        other.is_empty()
    }
}

impl<B: AsRef<[u8]>> PartialEq<Unescape<'_>> for Result<B, UnescapeError> {
    /// Compares the unescaper's outcome with a `Result`.
    ///
    /// This allows for precise testing of `Unescape` against either a
    /// successful outcome (`Ok(bytes)`) or a specific failure (`Err(error)`).
    fn eq(&self, unescape: &Unescape<'_>) -> bool {
        match self {
            Ok(expected_bytes) => unescape == expected_bytes,
            Err(expected_error) => {
                for result in unescape.clone() {
                    if let Err(actual_error) = result {
                        // The iterator's first error is its final outcome.
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
    /// use json_escape::explicit::unescape;
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
        // The crate parallel is easier
        crate::unescape(self.bytes) == crate::unescape(other.bytes)
    }
}

#[cfg(feature = "alloc")]
impl<'a> TryFrom<Unescape<'a>> for Cow<'a, [u8]> {
    type Error = UnescapeError;

    /// Efficiently collects the unescaped bytes into a `Cow<'a, [u8]>`.
    ///
    /// Returns `Cow::Borrowed` if no escape sequences were present, avoiding
    /// allocation. Otherwise, returns `Cow::Owned`. If an error occurs, it's
    /// returned immediately.
    fn try_from(mut value: Unescape<'a>) -> Result<Self, Self::Error> {
        match value.next() {
            None => Ok(Cow::Borrowed(b"")),
            Some(Ok(first)) => {
                if first.unescaped.is_none() {
                    // The first and only chunk has no unescaped part. No allocation needed.
                    Ok(Cow::Borrowed(first.literal))
                } else {
                    // An escape was processed. Must allocate and collect the rest.
                    let mut buf = Vec::with_capacity(value.bytes.len() + 16);
                    buf.extend_from_slice(first.literal);

                    // Helper to append a char directly to the Vec<u8> buffer.
                    // This should be more efficient than using an intermediate stack buffer.
                    let append_char = |buf: &mut Vec<u8>, c: char| {
                        // Reserve space for the character's bytes and write directly into the buffer.
                        let char_len = c.len_utf8();
                        let old_len = buf.len();
                        buf.resize(old_len + char_len, 0);
                        c.encode_utf8(&mut buf[old_len..]);
                    };

                    if let Some(c) = first.unescaped {
                        append_char(&mut buf, c);
                    }

                    for item in value {
                        let chunk = item?;
                        buf.extend_from_slice(chunk.literal);
                        if let Some(c) = chunk.unescaped {
                            append_char(&mut buf, c);
                        }
                    }
                    Ok(Cow::Owned(buf))
                }
            }
            Some(Err(e)) => Err(e),
        }
    }
}

/// A wrapper struct for implementing `fmt::Display` on an [`Unescape`] iterator.
pub struct DisplayUnescape<'a> {
    inner: Unescape<'a>,
    lossy: bool,
}

impl<'a> fmt::Display for DisplayUnescape<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for chunk_result in self.inner.clone() {
            match chunk_result {
                Ok(chunk) => {
                    let display_chunk = DisplayUnescapedChunk {
                        chunk: &chunk,
                        lossy: self.lossy,
                    };
                    write!(f, "{}", display_chunk)?;
                }
                Err(_) => return Err(fmt::Error), // Signal error to formatter
            }
        }
        Ok(())
    }
}

// Escape table: maps the byte after '\' to its escaped representation.
const UNESCAPE_TABLE: [Option<char>; 256] = {
    let mut tbl: [Option<char>; 256] = [None; 256];
    tbl[b'"' as usize] = Some('\"');
    tbl[b'\\' as usize] = Some('\\');
    tbl[b'/' as usize] = Some('/');
    tbl[b'b' as usize] = Some('\x08');
    tbl[b'f' as usize] = Some('\x0C');
    tbl[b'n' as usize] = Some('\n');
    tbl[b'r' as usize] = Some('\r');
    tbl[b't' as usize] = Some('\t');
    tbl
};

// --- Look-Up Table for Hex Decoding ---
const HEX: [Option<u8>; 256] = {
    let mut table = [None; 256];
    let mut i = 0;
    while i < 256 {
        table[i] = match i as u8 {
            b'0'..=b'9' => Some(i as u8 - b'0'),
            b'a'..=b'f' => Some(i as u8 - b'a' + 10),
            b'A'..=b'F' => Some(i as u8 - b'A' + 10),
            _ => None,
        };
        i += 1;
    }
    table
};

//==============================================================================
// Iterator Trait Implementations
//==============================================================================

#[cfg(feature = "alloc")]
mod iter_traits {
    use super::{EscapedChunk, UnescapedChunk};
    use alloc::string::String;
    use alloc::vec::Vec;

    /// Collects an iterator of escaped chunks into a single `String`.
    impl<'a> FromIterator<EscapedChunk<'a>> for String {
        #[inline]
        fn from_iter<I: IntoIterator<Item = EscapedChunk<'a>>>(iter: I) -> String {
            let mut s = String::new();
            s.extend(iter);
            s
        }
    }

    /// Extends a `String` with an iterator of escaped chunks.
    impl<'a> Extend<EscapedChunk<'a>> for String {
        #[inline]
        fn extend<I: IntoIterator<Item = EscapedChunk<'a>>>(&mut self, iter: I) {
            iter.into_iter().for_each(move |chunk| {
                self.push_str(chunk.literal);
                if let Some(escaped_str) = chunk.escaped {
                    self.push_str(escaped_str);
                }
            });
        }
    }

    /// Collects an iterator of unescaped chunks into a byte vector.
    impl<'a> FromIterator<UnescapedChunk<'a>> for Vec<u8> {
        #[inline]
        fn from_iter<I: IntoIterator<Item = UnescapedChunk<'a>>>(iter: I) -> Vec<u8> {
            let mut buf = Vec::new();
            buf.extend(iter);
            buf
        }
    }

    /// Extends a byte vector with an iterator of unescaped chunks.
    impl<'a> Extend<UnescapedChunk<'a>> for Vec<u8> {
        #[inline]
        fn extend<I: IntoIterator<Item = UnescapedChunk<'a>>>(&mut self, iter: I) {
            iter.into_iter().for_each(move |chunk| {
                self.extend_from_slice(chunk.literal);
                if let Some(c) = chunk.unescaped {
                    let char_len = c.len_utf8();
                    let old_len = self.len();
                    self.resize(old_len + char_len, 0);
                    c.encode_utf8(&mut self[old_len..]);
                }
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl<'a> EscapedChunk<'a> {
        /// Creates a new `EscapedChunk`.
        const fn new(literal: &'a str, escaped: Option<&'static str>) -> Self {
            Self { literal, escaped }
        }
    }

    impl<'a> UnescapedChunk<'a> {
        /// Creates a new `UnescapedChunk`.
        const fn new(literal: &'a [u8], unescaped: Option<char>) -> Self {
            Self { literal, unescaped }
        }
    }

    #[test]
    fn escape_chunks() {
        let mut it = escape_str("a\nb\"c");
        assert_eq!(
            it.next(),
            Some(EscapedChunk::new("a", Some(r#"\n"#))),
            "Chunk 1"
        );
        assert_eq!(
            it.next(),
            Some(EscapedChunk::new("b", Some(r#"\""#))),
            "Chunk 2"
        );
        assert_eq!(it.next(), Some(EscapedChunk::new("c", None)), "Chunk 3");
        assert_eq!(it.next(), None, "End of iterator");
    }

    #[test]
    fn unescape_chunks() {
        let mut it = unescape(br"xy\t\u0020z");
        assert_eq!(
            it.next().unwrap().unwrap(),
            UnescapedChunk::new(b"xy", Some('\t')),
            "Chunk 1"
        );
        assert_eq!(
            it.next().unwrap().unwrap(),
            UnescapedChunk::new(b"", Some(' ')),
            "Chunk 2"
        );
        assert_eq!(
            it.next().unwrap().unwrap(),
            UnescapedChunk::new(b"z", None),
            "Chunk 3"
        );
        assert_eq!(it.next(), None, "End of iterator");
    }

    #[test]
    fn test_escape_against_collected_string() {
        assert_eq!(
            escape_str("Hello, world!").collect::<String>(),
            "Hello, world!"
        );
        assert_eq!(escape_str("a\"b").collect::<String>(), r#"a\"b"#);
        assert_eq!(escape_str("\0").collect::<String>(), r#"\u0000"#);
        assert_eq!(
            escape_str("path/to/file").collect::<String>(),
            r#"path/to/file"#
        );

        escape_str(r#"Unicode test: éàçüö. Emoji: 😀. More symbols: ❤️✅."#).for_each(|_| {});
    }

    #[test]
    fn test_unescape_against_collected_string() {
        assert_eq!(
            unescape(br"Hello, world!").decode_utf8().unwrap(),
            "Hello, world!"
        );
        assert_eq!(unescape(br"a\nb").decode_utf8().unwrap(), "a\nb");
        assert_eq!(unescape(br"\uD83D\uDE00").decode_utf8().unwrap(), "😀");
    }

    #[test]
    fn unescape_error_propagation() {
        let mut it = unescape(br"valid\k");

        // A better design: the error is the *only* thing that comes out for that step.
        // The current implementation bundles the literal with the result of the escape.
        // Let's stick with that.
        let first_chunk = it.next().unwrap();
        assert!(matches!(first_chunk, Err(UnescapeError { .. })));
    }

    // Inspired by and copied from memchr
    #[test]
    fn sync_regression() {
        use core::panic::{RefUnwindSafe, UnwindSafe};

        fn assert_send_sync<T: Send + Sync + UnwindSafe + RefUnwindSafe>() {}
        assert_send_sync::<Unescape<'_>>();
        assert_send_sync::<Escape<'_>>();

        assert_send_sync::<UnescapedChunk<'_>>();
        assert_send_sync::<EscapedChunk<'_>>();
    }
}
