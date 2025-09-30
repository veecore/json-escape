//! Provides low-level, granular, token-based JSON string processing.
//!
//! This module offers the most fundamental building blocks for both escaping and
//! unescaping. It provides iterators, [`UnescapeTokens`] and [`EscapeTokens`],
//! that walk a byte/string slice and yield tokens. This approach is highly flexible
//! and composable, allowing consumers to handle the data in a zero-copy,
//! streaming fashion for literal (non-processed) parts.
//!
//! ## Unescaping
//!
//! The [`UnescapeTokens`] iterator yields [`UnescapedToken`]s, separating literal
//! byte slices from single unescaped `char`s. This ensures that in the case of an
//! error (e.g., an invalid escape sequence), all preceding valid literal parts have
//! already been successfully yielded.
//!
//! ## Escaping
//!
//! The [`EscapeTokens`] iterator yields [`EscapedToken`]s, separating literal
//! string slices from the `&'static str` representation of an escaped character.
//! This allows for efficient, allocation-free iteration over a string to produce
//! its JSON-escaped form.

#[cfg(feature = "alloc")]
use crate::DecodeUtf8Error;
use crate::{
    InvalidEscapeError, InvalidHexError, LoneSurrogateError, UnescapeError, UnescapeErrorKind,
};
use core::{
    fmt::{self, Write as _},
    iter::FusedIterator,
};
use memchr::memchr;

#[cfg(feature = "alloc")]
use alloc::{borrow::Cow, string::String, vec::Vec};

//==============================================================================
// Escaping
//==============================================================================

/// Creates an iterator that yields tokens of an escaped JSON string.
///
/// See the [module-level documentation](self) for more details.
#[inline]
pub fn escape_str(s: &str) -> EscapeTokens<'_> {
    EscapeTokens {
        bytes: s.as_bytes(),
    }
}

/// A token representing a piece of an escaped JSON string.
///
/// This enum is the item yielded by the [`EscapeTokens`] iterator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EscapedToken<'a> {
    /// A slice of the original input that did not require escaping.
    Literal(&'a str),
    /// The `&'static str` representation of an escaped character (e.g., `r#"\n"#`).
    Escaped(&'static str),
}

impl<'a> EscapedToken<'a> {
    #[inline(always)]
    pub(crate) fn as_str(&self) -> &'a str {
        match self {
            EscapedToken::Literal(s) => s,
            EscapedToken::Escaped(s) => s,
        }
    }
}

impl fmt::Display for EscapedToken<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// An iterator over a string that yields [`EscapedToken`]s.
///
/// This is a low-level API for producing a JSON-escaped representation of a
/// string slice without allocation. It yields borrowed string slices for literal
/// parts and static string slices for the escape sequences themselves.
#[derive(Clone, Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct EscapeTokens<'a> {
    pub(crate) bytes: &'a [u8],
}

impl<'a> EscapeTokens<'a> {
    /// Creates a new tokenizing escaper for the given string slice.
    #[inline]
    pub const fn new(s: &'a str) -> Self {
        Self {
            bytes: s.as_bytes(),
        }
    }

    #[inline(always)]
    pub(crate) fn escape(byte: u8) -> Option<&'static str> {
        ESCAPE_TABLE[byte as usize]
    }

    /// Splits the slice at the first byte that needs to be escaped.
    ///
    /// The first element of the returned tuple is the literal part, which is
    /// guaranteed to be valid UTF-8. The second is the rest of the slice,
    /// which starts with an escapable byte, or is empty.
    ///
    /// # SAFETY
    ///
    /// The input byte slice `bytes` must be valid UTF-8. This is because the
    /// function uses `from_utf8_unchecked`, relying on the fact that all
    /// escapable characters are single-byte ASCII and thus cannot occur in
    /// the middle of a multi-byte UTF-8 sequence.
    #[inline(always)]
    pub(crate) unsafe fn split_at_escape(bytes: &[u8]) -> (&str, &[u8]) {
        // Find the first byte that needs escaping.
        let pos = match Self::find_escape_char(bytes) {
            // Found a backslash, the literal is the part before it.
            Some(p) => p,
            // No more backslashes, the rest of the slice is a literal.
            None => bytes.len(),
        };

        let (literal_bytes, rest) = bytes.split_at(pos);
        // SAFETY: `find_escape_char` guarantees `pos` is on a UTF-8 boundary
        // because escapable characters are single-byte ASCII.
        (
            unsafe { std::str::from_utf8_unchecked(literal_bytes) },
            rest,
        )
    }

    // Not public API. Exposed for test
    #[doc(hidden)]
    // This is the SIMD version, compiled only when the "simd" feature is enabled on nightly build.
    #[cfg(all(feature = "simd", nightly))]
    #[inline]
    pub fn find_escape_char(bytes: &[u8]) -> Option<usize> {
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

    // Not public API. Exposed for test
    #[doc(hidden)]
    #[cfg(all(feature = "simd", not(nightly), target_arch = "x86_64"))]
    #[inline]
    pub fn find_escape_char(bytes: &[u8]) -> Option<usize> {
        // This is the stable Rust path using explicit CPU intrinsics.
        // It's guarded by cfg flags to only compile on x86_64 with the simd feature.
        use std::arch::x86_64::*;

        let mut i = 0;
        const LANES: usize = 16; // SSE2 works on 128-bit registers, which is 16 bytes.

        // On x86_64, we can tell the compiler to use SSE2 features in this specific function.
        // This is safe because we've already checked the target architecture.
        // SAFETY: calling this unsafe function is only safe if the caller ensures:
        //  - the CPU supports SSE2, and
        //  - i + LANES <= bytes.len()
        #[target_feature(enable = "sse2")]
        unsafe fn find_in_chunk(bytes: &[u8], i: usize) -> Option<usize> {
            // Safety check: ensure the 16 bytes we will load are inside the slice.
            // This is a debug-time assertion to help catch incorrect call.
            debug_assert!(
                i + LANES <= bytes.len(),
                "find_in_chunk: attempted to load past end of slice"
            );

            // Load 16 bytes of data from the slice.
            // SAFETY: caller must guarantee `i + LANES <= bytes.len()`. We assert that above.
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
            let combined_mask =
                _mm_or_si128(lt_space_mask, _mm_or_si128(eq_quote_mask, eq_slash_mask));

            // Create a bitmask to find the first match.
            let mask = _mm_movemask_epi8(combined_mask);

            if mask != 0 {
                Some(i + mask.trailing_zeros() as usize)
            } else {
                None
            }
        }

        if cfg!(target_feature = "sse2") {
            // Main loop (vectorized)
            while i + LANES <= bytes.len() {
                // Safety: calling `find_in_chunk` is safe here because:
                //  - we've checked CPU supports SSE2 via is_x86_feature_detected!
                //  - loop condition ensures `i + LANES <= bytes.len()`, matching the debug_assert in the function.
                if let Some(result) = unsafe { find_in_chunk(bytes, i) } {
                    return Some(result);
                }
                i += LANES;
            }
        } else {
            // CPU doesn't support SSE2: fall through to scalar path below.
            // (We intentionally do not attempt to call the sse2 function.)
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

    // Not public API. Exposed for test
    // A fallback for when SIMD feature is off.
    #[doc(hidden)]
    #[cfg(not(feature = "simd"))]
    #[inline]
    pub fn find_escape_char(bytes: &[u8]) -> Option<usize> {
        use core::mem::size_of;

        const WORD_SIZE: usize = size_of::<usize>();
        const THRESH: u8 = 0x20; // control threshold

        // helper: repeat a byte across a usize (works for any usize width)
        const fn repeat(b: u8) -> usize {
            let mut m: usize = 0;
            let mut i = 0;
            while i < WORD_SIZE {
                m = (m << 8) | (b as usize);
                i += 1;
            }
            m
        }

        // Precompute masks as constants
        const ONE_MASK: usize = repeat(0x01);
        const MSB_MASK: usize = repeat(0x80);
        const QUOTE_MASK: usize = repeat(b'"');
        const SLASH_MASK: usize = repeat(b'\\');
        const THR_MASK: usize = repeat(THRESH);

        let mut i = 0usize;
        while i + WORD_SIZE <= bytes.len() {
            // SAFETY: we checked bounds; read_unaligned is allowed for any alignment.
            let word = unsafe { (bytes.as_ptr().add(i) as *const usize).read_unaligned() };

            // equality tests (SWAR zero-byte detection on XOR)
            let xq = word ^ QUOTE_MASK;
            let quote_bits = (xq.wrapping_sub(ONE_MASK) & !xq) & MSB_MASK;

            let xs = word ^ SLASH_MASK;
            let slash_bits = (xs.wrapping_sub(ONE_MASK) & !xs) & MSB_MASK;

            // control: detect bytes < 0x20 using subtract+~word+msb trick
            // If any byte b satisfies b < 0x20 then the corresponding MSB bit in control_bits is set.
            let control_bits = (word.wrapping_sub(THR_MASK) & !word) & MSB_MASK;

            // combined mask: MSB-bit set per candidate byte
            let combined = quote_bits | slash_bits | control_bits;

            if combined != 0 {
                // Find earliest matching byte inside this word in a portable way:
                // - on little-endian the least-significant set bit corresponds to the earliest byte
                // - on big-endian the most-significant set bit corresponds to the earliest byte
                let byte_index = if cfg!(target_endian = "little") {
                    (combined.trailing_zeros() as usize) / 8
                } else {
                    (combined.leading_zeros() as usize) / 8
                };
                return Some(i + byte_index);
            }

            i += WORD_SIZE;
        }

        // tail bytes
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

    #[cfg(all(feature = "simd", not(nightly), not(target_arch = "x86_64")))]
    compile_error! { "simd requires nightly or target_arch = \"x86_64\"" }
}

impl<'a> Iterator for EscapeTokens<'a> {
    type Item = EscapedToken<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bytes.is_empty() {
            return None;
        }

        if let Some(escaped) = Self::escape(self.bytes[0]) {
            // --- Handle Escape ---
            // An escapable byte is at the beginning of the slice.
            self.bytes = &self.bytes[1..];
            Some(EscapedToken::Escaped(escaped))
        } else {
            // --- Handle Literal ---
            // SAFETY: Input is string
            let (literal, rest) = unsafe { Self::split_at_escape(self.bytes) };
            self.bytes = rest;
            Some(EscapedToken::Literal(literal))
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

impl<'a> FusedIterator for EscapeTokens<'a> {}

impl fmt::Display for EscapeTokens<'_> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for token in self.clone() {
            f.write_str(token.as_str())?;
        }
        Ok(())
    }
}

#[cfg(feature = "alloc")]
impl<'a> From<EscapeTokens<'a>> for Cow<'a, str> {
    /// Efficiently collects the escaped parts into a `Cow<'a, str>`.
    ///
    /// This implementation is optimized to avoid allocation if possible:
    /// - If the input string requires **no escaping**, it returns `Cow::Borrowed`
    ///   with a slice of the original string.
    /// - If escaping is needed, it allocates a `String` and returns `Cow::Owned`.
    fn from(mut iter: EscapeTokens<'a>) -> Self {
        match iter.next() {
            None => Cow::Borrowed(""),
            Some(EscapedToken::Literal(s)) if iter.bytes.is_empty() => {
                // No escape in the first (and only) chunk, so no escaping was needed.
                Cow::Borrowed(s)
            }
            Some(first) => {
                // Escaping occurred. We must allocate.
                let mut s = String::with_capacity(first.as_str().len() + iter.bytes.len());
                s.push_str(first.as_str());
                s.extend(iter);
                Cow::Owned(s)
            }
        }
    }
}

//==============================================================================
// Unescaping
//==============================================================================

/// Creates an iterator that yields tokens of an unescaped JSON string.
///
/// See the [module-level documentation](self) for more details.
#[inline]
pub fn unescape<I: AsRef<[u8]> + ?Sized>(input: &I) -> UnescapeTokens<'_> {
    UnescapeTokens {
        bytes: input.as_ref(),
    }
}

/// A token representing a piece of an unescaped JSON string.
///
/// This enum is the item yielded by the [`UnescapeTokens`] iterator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnescapedToken<'a> {
    /// A slice of the original input that did not require unescaping.
    Literal(&'a [u8]),
    /// A single character that was unescaped from an escape sequence.
    Unescaped(char),
}

impl UnescapedToken<'_> {
    /// Returns a wrapper that implements [`fmt::Display`].
    ///
    /// If the token is a `Literal` containing invalid UTF-8, a `fmt::Error`
    /// is returned, which will cause `format!` and friends to panic.
    pub fn display_utf8(&self) -> DisplayUnescapedToken<'_> {
        DisplayUnescapedToken {
            token: self,
            lossy: true,
        }
    }

    /// Returns a wrapper that implements [`fmt::Display`] for lossy UTF-8 decoding.
    ///
    /// If the token is a `Literal` containing invalid UTF-8, it will be replaced
    /// with the replacement character.
    pub fn display_utf8_lossy(&self) -> DisplayUnescapedToken<'_> {
        DisplayUnescapedToken {
            token: self,
            lossy: true,
        }
    }

    #[inline(always)]
    const fn len(&self) -> usize {
        match self {
            UnescapedToken::Literal(literal) => literal.len(),
            UnescapedToken::Unescaped(ch) => ch.len_utf8(),
        }
    }
}

/// Helper struct for safely displaying an [`DisplayUnescapedToken`].
pub struct DisplayUnescapedToken<'a> {
    token: &'a UnescapedToken<'a>,
    lossy: bool,
}

impl fmt::Display for DisplayUnescapedToken<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.token {
            UnescapedToken::Literal(bytes) => crate::display_bytes_utf8(bytes, f, self.lossy),
            UnescapedToken::Unescaped(c) => f.write_char(*c),
        }
    }
}

/// An iterator over a byte slice that yields [`UnescapedToken`]s.
///
/// This is the foundational, low-level unescaping API. It processes the byte
/// slice, yielding runs of literal bytes as borrowed slices and successfully
/// parsed escape sequences as `char`s.
///
/// If an error is encountered while parsing an escape, the iterator will yield
/// an `Err` and all subsequent calls to `next()` will return `None`.
///
/// Created by [`UnescapeTokens::new`].
#[derive(Clone, Debug)]
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct UnescapeTokens<'a> {
    bytes: &'a [u8],
}

impl<'a> UnescapeTokens<'a> {
    /// Creates a new tokenizing unescaper for the given byte slice.
    #[inline]
    pub const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes }
    }

    /// Returns the remaining unprocessed slice of bytes.
    ///
    /// If the iterator encounters an `UnexpectedEof` error, this method can be
    /// used to retrieve the incomplete segment that needs to be stitched with
    /// the next chunk in a streaming context.
    #[inline]
    pub const fn remnant(&self) -> &'a [u8] {
        self.bytes
    }

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
    /// This is similar to [`UnescapeTokens::decode_utf8`] but replaces any invalid UTF-8 sequences
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
    pub fn display_utf8(self) -> DisplayUnescapeTokens<'a> {
        DisplayUnescapeTokens {
            inner: self,
            lossy: false,
        }
    }

    /// Returns a wrapper that implements [`fmt::Display` for lossy UTF-8 decoding.
    ///
    /// Invalid UTF-8 sequences will be replaced with the replacement character.
    /// An unescaping error will still result in a `fmt::Error`.
    pub fn display_utf8_lossy(self) -> DisplayUnescapeTokens<'a> {
        DisplayUnescapeTokens {
            inner: self,
            lossy: true,
        }
    }

    /// Splits the slice at the first backslash `\`.
    ///
    /// The first element of the returned tuple is the literal part before the
    /// backslash. The second is the rest of the slice, which starts with the
    /// backslash, or is empty if no backslash was found.
    #[inline(always)]
    pub(crate) fn split_at_escape(bytes: &'a [u8]) -> (&'a [u8], &'a [u8]) {
        let pos = match memchr(b'\\', bytes) {
            // Found a backslash, the literal is the part before it.
            Some(p) => p,
            // No more backslashes, the rest of the slice is a literal.
            None => bytes.len(),
        };

        let (literal, rest) = bytes.split_at(pos);
        (literal, rest)
    }

    /// Parses any escape sequence (`\uXXXX`, '\n', e.t.c).
    /// The input slice `bytes` must be positioned *after* the `\`.
    ///
    /// On error, returns an `Err` and the input slice may be modified.
    #[inline(always)]
    pub(crate) fn handle_escape(bytes: &mut &'a [u8]) -> Result<char, UnescapeError> {
        match bytes.first() {
            Some(b'u') => {
                // Advance past 'u' and parse unicode
                *bytes = &bytes[1..];
                Self::handle_unicode_escape(bytes)
            }
            Some(&byte) => {
                // Simple 1-char escape like \n, \t, etc.
                match UNESCAPE_TABLE[byte as usize] {
                    Some(c) => {
                        *bytes = &bytes[1..];
                        Ok(c)
                    }
                    None => {
                        Err(UnescapeError {
                            kind: UnescapeErrorKind::InvalidEscape(InvalidEscapeError {
                                found: byte,
                            }),
                            // The invalid character is 1 byte after '\'.
                            offset: 1,
                        })
                    }
                }
            }
            None => {
                // Dangling backslash at the end of input
                Err(UnescapeError {
                    kind: UnescapeErrorKind::UnexpectedEof,
                    // EOF occurred 1 byte after '\'.
                    offset: 1,
                })
            }
        }
    }

    /// Parses a unicode escape sequence `\uXXXX` which may be a surrogate pair.
    /// The input slice `bytes` must be positioned *after* the `\u`.
    ///
    /// On success, returns the parsed `char` and advances the slice.
    /// On error, returns an `Err` and the input slice may be modified.
    #[inline(always)]
    fn handle_unicode_escape(bytes: &mut &'a [u8]) -> Result<char, UnescapeError> {
        // Parse first 4 hex digits (\uXXXX)
        //
        // The slice starts *after* '\u'. The first hex digit is at offset 2 from '\'.
        let first = Self::parse_hex4(bytes, 2)?;
        *bytes = &bytes[4..];

        // High surrogate → must be followed by another \uXXXX low surrogate
        if (0xD800..=0xDBFF).contains(&first) {
            // A high surrogate must be followed by a `\u` sequence.
            // We check for at least 2 bytes and that they are `\` and `u`.
            #[allow(clippy::get_first)]
            match (bytes.get(0), bytes.get(1)) {
                (Some(b'\\'), Some(b'u')) => {
                    // We have `\u`, so we now expect 4 more hex digits for the low surrogate.
                    // The slice for `parse_hex4` starts after `\u`, and the overall offset
                    // from the beginning of the original escape is 8 (`\uXXXX\u`).
                    match Self::parse_hex4(&bytes[2..], 8) {
                        Ok(low) if (0xDC00..=0xDFFF).contains(&low) => {
                            // Valid low surrogate found. Combine them.
                            let high_t = first as u32;
                            let low_t = low as u32;
                            let code = 0x10000 + (((high_t - 0xD800) << 10) | (low_t - 0xDC00));
                            let result_char = char::from_u32(code).expect(
                                "valid surrogate pair math should always produce a valid char",
                            );

                            // Advance the slice past the entire low surrogate sequence.
                            *bytes = &bytes[6..];
                            return Ok(result_char);
                        }
                        Ok(_) => {
                            // We parsed `\uXXXX`, but the value was not a valid low surrogate.
                            // This makes the initial high surrogate a "lone surrogate".
                            return Err(UnescapeError {
                                kind: UnescapeErrorKind::LoneSurrogate(LoneSurrogateError {
                                    surrogate: first,
                                }),
                                offset: 6,
                            });
                        }
                        Err(err) => {
                            // `parse_hex4` failed (e.g., incomplete hex, invalid char).
                            // Propagate the error.
                            return Err(err);
                        }
                    }
                }
                (Some(b'\\'), None) => {
                    return Err(UnescapeError {
                        kind: UnescapeErrorKind::UnexpectedEof,
                        offset: 7,
                    });
                }
                (None, None) => {
                    // The input ended immediately after the high surrogate.
                    return Err(UnescapeError {
                        kind: UnescapeErrorKind::UnexpectedEof,
                        offset: 6,
                    });
                }
                // Something else after high surrogate → LoneSurrogate
                _ => {
                    // There are other characters, but they don't form a `\u` sequence.
                    return Err(UnescapeError {
                        kind: UnescapeErrorKind::LoneSurrogate(LoneSurrogateError {
                            surrogate: first,
                        }),
                        offset: 6,
                    });
                }
            }
        }

        // Not a surrogate → normal path
        match char::from_u32(first as u32) {
            Some(c) => Ok(c),
            None => {
                // The parsed value is not a valid char (e.g., it's a lone low surrogate).
                Err(UnescapeError {
                    kind: UnescapeErrorKind::LoneSurrogate(LoneSurrogateError { surrogate: first }),
                    // The error is detected after consuming `\uXXXX` (6 bytes total from '\').
                    offset: 6,
                })
            }
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
            for (i, &b) in slice.iter().enumerate() {
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

impl<'a> Iterator for UnescapeTokens<'a> {
    type Item = Result<UnescapedToken<'a>, UnescapeError>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.bytes.is_empty() {
            return None;
        }

        // Check if the next part is an escape sequence or a literal.
        if self.bytes[0] == b'\\' {
            // --- Handle Escape Sequence ---
            Some({
                // TODO: Try abstract... repeated in explicit
                // rest starts with '\\'
                let mut remainder = &self.bytes[1..];
                match UnescapeTokens::handle_escape(&mut remainder) {
                    Ok(unescaped_char) => {
                        self.bytes = remainder;
                        Ok(UnescapedToken::Unescaped(unescaped_char))
                    }
                    Err(err) => Err(err),
                }
            })
        } else {
            // --- Handle Literal ---
            let (literal, rest) = Self::split_at_escape(self.bytes);
            self.bytes = rest;
            Some(Ok(UnescapedToken::Literal(literal)))
        }
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

impl<'a> FusedIterator for UnescapeTokens<'a> {}

#[cfg(feature = "alloc")]
impl<'a> TryFrom<UnescapeTokens<'a>> for Cow<'a, [u8]> {
    type Error = UnescapeError;

    /// Efficiently collects the unescaped bytes into a `Cow<'a, [u8]>`.
    ///
    /// Returns `Cow::Borrowed` if no escape sequences were present, avoiding
    /// allocation. Otherwise, returns `Cow::Owned`. If an error occurs, it's
    /// returned immediately.
    fn try_from(mut value: UnescapeTokens<'a>) -> Result<Self, Self::Error> {
        match value.next() {
            None => Ok(Cow::Borrowed(b"")),
            Some(Ok(UnescapedToken::Literal(literal))) if value.bytes.is_empty() => {
                // The first and only token is a literal. No allocation needed.
                Ok(Cow::Borrowed(literal))
            }
            Some(Ok(first_token)) => {
                // An escape was processed or there are more tokens. Must allocate.
                let mut buf = Vec::with_capacity(first_token.len() + value.bytes.len());

                let process_token = |buf: &mut Vec<u8>, token: UnescapedToken| match token {
                    UnescapedToken::Literal(bytes) => buf.extend_from_slice(bytes),
                    UnescapedToken::Unescaped(c) => {
                        append_char(buf, c);
                    }
                };

                process_token(&mut buf, first_token);
                for item in value {
                    process_token(&mut buf, item?);
                }

                Ok(Cow::Owned(buf))
            }
            Some(Err(e)) => Err(e),
        }
    }
}

/// A wrapper struct for implementing `fmt::Display` on an [`UnescapeTokens`] iterator.
pub struct DisplayUnescapeTokens<'a> {
    inner: UnescapeTokens<'a>,
    lossy: bool,
}

impl<'a> fmt::Display for DisplayUnescapeTokens<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for chunk_result in self.inner.clone() {
            match chunk_result {
                Ok(token) => {
                    let display_chunk = DisplayUnescapedToken {
                        token: &token,
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

// Not public API. Exposed for test
#[doc(hidden)]
// A simple boolean-like lookup table for SIMD.
// 0 = no escape needed, 1 = escape needed.
// This is very compact (256 bytes) and fits easily in the L1 cache.
#[allow(unused)]
pub const ESCAPE_DECISION_TABLE: [u8; 256] = {
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

// Helper to append a char directly to the Vec<u8> buffer.
// This should be more efficient than using an intermediate stack buffer.
#[inline]
pub(crate) fn append_char(buf: &mut Vec<u8>, c: char) {
    // Reserve space for the character's bytes and write directly into the buffer.
    let char_len = c.len_utf8();
    let old_len = buf.len();
    buf.resize(old_len + char_len, 0);
    c.encode_utf8(&mut buf[old_len..]);
}

//==============================================================================
// Iterator Trait Implementations
//==============================================================================

#[cfg(feature = "alloc")]
mod iter_traits {
    use super::{EscapedToken, UnescapedToken, append_char};
    use alloc::string::String;
    use alloc::vec::Vec;

    /// Collects an iterator of escaped chunks into a single `String`.
    impl<'a> FromIterator<EscapedToken<'a>> for String {
        #[inline]
        fn from_iter<I: IntoIterator<Item = EscapedToken<'a>>>(iter: I) -> String {
            let mut s = String::new();
            s.extend(iter);
            s
        }
    }

    /// Extends a `String` with an iterator of escaped tokens.
    impl<'a> Extend<EscapedToken<'a>> for String {
        #[inline]
        fn extend<I: IntoIterator<Item = EscapedToken<'a>>>(&mut self, iter: I) {
            iter.into_iter().for_each(move |token| {
                self.push_str(token.as_str());
            });
        }
    }

    /// Collects an iterator of unescaped chunks into a byte vector.
    impl<'a> FromIterator<UnescapedToken<'a>> for Vec<u8> {
        #[inline]
        fn from_iter<I: IntoIterator<Item = UnescapedToken<'a>>>(iter: I) -> Vec<u8> {
            let mut buf = Vec::new();
            buf.extend(iter);
            buf
        }
    }

    /// Extends a byte vector with an iterator of unescaped chunks.
    impl<'a> Extend<UnescapedToken<'a>> for Vec<u8> {
        #[inline]
        fn extend<I: IntoIterator<Item = UnescapedToken<'a>>>(&mut self, iter: I) {
            iter.into_iter().for_each(move |token| match token {
                UnescapedToken::Literal(literal) => self.extend_from_slice(literal),
                UnescapedToken::Unescaped(ch) => append_char(self, ch),
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_string() {
        let mut iter = UnescapeTokens::new(b"");
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_pure_literal() {
        let mut iter = UnescapeTokens::new(b"hello world");
        assert_eq!(
            iter.next(),
            Some(Ok(UnescapedToken::Literal(b"hello world")))
        );
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_simple_escapes() {
        let mut iter = UnescapeTokens::new(b"a\\nb\\tc");
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Literal(b"a"))));
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Unescaped('\n'))));
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Literal(b"b"))));
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Unescaped('\t'))));
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Literal(b"c"))));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_starts_with_escape() {
        let mut iter = UnescapeTokens::new(b"\\nhello");
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Unescaped('\n'))));
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Literal(b"hello"))));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_ends_with_escape() {
        let mut iter = UnescapeTokens::new(b"hello\\n");
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Literal(b"hello"))));
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Unescaped('\n'))));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_unicode_and_surrogate() {
        let mut iter = UnescapeTokens::new(b"A is \\u0041, smiley is \\uD83D\\uDE00!");
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Literal(b"A is "))));
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Unescaped('A'))));
        assert_eq!(
            iter.next(),
            Some(Ok(UnescapedToken::Literal(b", smiley is ")))
        );
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Unescaped('😀'))));
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Literal(b"!"))));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_invalid_escape_yields_literal_first() {
        let mut iter = UnescapeTokens::new(b"ValidPart\\zInvalid");
        // First, we get the valid literal part. THIS is the key fix.
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Literal(b"ValidPart"))));
        // Then, we get the error.
        let err = iter.next().unwrap().unwrap_err();
        assert_eq!(
            err,
            UnescapeError {
                kind: UnescapeErrorKind::InvalidEscape(InvalidEscapeError { found: b'z' }),
                offset: 1,
            }
        );
        // The iterator should keep erroring
        assert_eq!(iter.remnant(), b"\\zInvalid");
        assert_eq!(iter.next(), Some(Err(err)));
    }

    #[test]
    fn test_sticky_error_behavior() {
        let mut iter = UnescapeTokens::new(b"a\\zb");
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Literal(b"a"))));

        // First error
        let err1 = iter.next().unwrap().unwrap_err();
        assert_eq!(
            err1.kind,
            UnescapeErrorKind::InvalidEscape(InvalidEscapeError { found: b'z' })
        );
        assert_eq!(iter.remnant(), b"\\zb");

        // Second call should yield the same error
        let err2 = iter.next().unwrap().unwrap_err();
        assert_eq!(err1, err2);
        assert_eq!(iter.remnant(), b"\\zb"); // Remnant is unchanged
    }

    #[test]
    fn test_incomplete_escape_at_end() {
        let mut iter = UnescapeTokens::new(b"ValidPart\\u12");
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Literal(b"ValidPart"))));

        // Before consuming the error, check the remnant.
        assert_eq!(iter.remnant(), b"\\u12");

        let err = iter.next().unwrap().unwrap_err();
        assert_eq!(
            err,
            UnescapeError {
                kind: UnescapeErrorKind::UnexpectedEof,
                offset: 4,
            }
        );

        assert_eq!(iter.remnant(), b"\\u12");
        assert_eq!(iter.next(), Some(Err(err)));
    }

    #[test]
    fn test_dangling_backslash() {
        let mut iter = UnescapeTokens::new(b"end with \\");
        assert_eq!(iter.next(), Some(Ok(UnescapedToken::Literal(b"end with "))));
        let err = iter.next().unwrap().unwrap_err();
        assert_eq!(
            err,
            UnescapeError {
                kind: UnescapeErrorKind::UnexpectedEof,
                offset: 1,
            }
        );
        assert_eq!(iter.next(), Some(Err(err)));
    }

    #[test]
    fn test_display_unescape_tokens() {
        let iter = UnescapeTokens::new(b"hello \\u0041\\nworld");
        let display = iter.display_utf8();
        assert_eq!(alloc::format!("{}", display), "hello A\nworld");
    }

    #[test]
    fn test_display_unescape_error() {
        let iter = UnescapeTokens::new(b"hello\\z");
        let mut out = String::new();
        write!(out, "{}", iter.display_utf8_lossy()).unwrap_err();
        // Formatting fails, but doesn't panic. The result is just truncated.
        // The exact output may vary, but we test that it doesn't contain the bad part.
        assert!(out.starts_with("hello"));
    }

    // --- Escape Tests ---
    #[test]
    fn test_escape_no_escapes() {
        let mut iter = EscapeTokens::new("hello world");
        assert_eq!(iter.next(), Some(EscapedToken::Literal("hello world")));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_escape_simple() {
        let mut iter = EscapeTokens::new("hello\nworld");
        assert_eq!(iter.next(), Some(EscapedToken::Literal("hello")));
        assert_eq!(iter.next(), Some(EscapedToken::Escaped(r#"\n"#)));
        assert_eq!(iter.next(), Some(EscapedToken::Literal("world")));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_display_escape_tokens() {
        let iter = EscapeTokens::new("a\"b\tc");
        assert_eq!(alloc::format!("{}", iter), r#"a\"b\tc"#);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_escape_to_cow_borrowed() {
        let iter = EscapeTokens::new("no escapes here");
        let cow: Cow<'_, str> = iter.into();
        assert!(matches!(cow, Cow::Borrowed(_)));
        assert_eq!(cow, "no escapes here");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_escape_to_cow_owned() {
        let iter = EscapeTokens::new("has\n an escape");
        let cow: Cow<'_, str> = iter.into();
        assert!(matches!(cow, Cow::Owned(_)));
        assert_eq!(cow, r#"has\n an escape"#);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_unescape_to_cow_borrowed() {
        let iter = UnescapeTokens::new(b"no escapes here");
        let cow: Cow<'_, [u8]> = iter.try_into().unwrap();
        assert!(matches!(cow, Cow::Borrowed(_)));
        assert_eq!(*cow, *b"no escapes here");
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn test_unescape_to_cow_owned() {
        let iter = UnescapeTokens::new(b"has\\n an escape");
        let cow: Cow<'_, [u8]> = iter.try_into().unwrap();
        assert!(matches!(cow, Cow::Owned(_)));
        assert_eq!(*cow, *b"has\n an escape");
    }
}

#[cfg(test)]
mod find_escape_char_tests {
    use std::format;

    use super::{ESCAPE_DECISION_TABLE, EscapeTokens};

    /// Helper function to run a single test case and provide a clear error message on failure.
    fn run_test(input: &str, expected: Option<usize>, case_name: &str) {
        let result = EscapeTokens::find_escape_char(input.as_bytes());
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

            let result = EscapeTokens::find_escape_char(&test_bytes);
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
