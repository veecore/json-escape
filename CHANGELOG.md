# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),  
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.3.0] - 2025-09-30

### 🎉 Added

* **Streaming Unescape API**: A new `stream` module provides the `UnescapeStream` struct for high-performance, allocation-free processing of chunked byte slices. It's perfect for I/O-bound applications as it correctly handles escape sequences that are split across buffer boundaries.
* **Low-Level Token API**: A new `token` module introduces a granular, iterator-based API (`UnescapeTokens` and `EscapeTokens`). This provides a more flexible, zero-copy foundation for building custom string processors.

### 🚀 Performance

* **SWAR-based Escape Finding**: Replaced the byte-by-byte scan with a SWAR (SIMD Within A Register) algorithm, making escape detection significantly faster in common scenarios:
    * **~2.5× faster** on strings with no escapes.
    * **~1.8× faster** on strings with sparse escapes.
    * **~2.2× faster** on typical Unicode-heavy strings.

### 🐞 Fixed

* **Corrected EOF in Surrogate Pairs**: Fixed a bug where an incomplete surrogate pair at the end of the input (e.g., `\uD83D\u`) was incorrectly reported as a `LoneSurrogate` error. It is now correctly identified as an `UnexpectedEof` error, with regression tests to prevent recurrence.

## [0.2.0] - 2025-09-26

### Fixed

  * **Prevented pointer provenance loss in iterators** (`unescape` and `escape`). The internal state slice (`self.bytes`) now correctly points to an empty subslice of the original input buffer after completion. This prevents potential pointer arithmetic underflow and Undefined Behavior (UB).

### Refactoring

  * Major internal refactoring of the `unescape` implementation. The core logic has been moved from `lib.rs` into **`explicit.rs`**, and the public `unescape` functions now use the faster, dedicated **`explicit::Unescape`** iterator. This improves code organization and developer focus.

### ⚠️ Breaking Change (Behavioral)

  * **Error state truncation is now immediate** when using **`.display_utf8_lossy()`** after encountering an invalid escape sequence (e.g., `\z`, incomplete Unicode).
      * Previously, the iterator could yield some leading, successfully unescaped data before the error stopped processing, allowing partial data to be displayed.
      * The new, optimized iterator structure stops processing immediately upon error discovery, resulting in **no partial data** being yielded or displayed.

## [0.1.3] - 2025-09-26

### Fixed

- **Corrected offset for Unicode escape errors.** Previously, an incorrect manual adjustment of `+2` was applied to the error offset, causing invalid escape sequences like `\uD83D` to report the wrong position. This change removes the redundant adjustment, ensuring error positions are now reported accurately.

## [0.1.2] - 2025-09-25

### Added

-   **New `explicit` module** providing an alternative, fine-grained streaming API for both escaping and unescaping.
    -   The iterators in this module yield structured `EscapedChunk` and `UnescapedChunk` types, allowing users to inspect literal text and modified characters separately.
    -   This new API offers improved performance in several unescaping scenarios (e.g., up to 2x faster pure iteration with dense/sparse escapes).

### Changed

-   Updated crate description in `Cargo.toml` and README to better highlight **ergonomics, correctness, and RFC compliance** alongside high performance.

### Fixed

  - **Corrected a critical panic** in the SIMD-accelerated escape logic that occurred when processing strings containing multi-byte Unicode characters on x86\_64 targets.
  
***

## [0.1.1] - 2025-09-19
### Fixed
- **Unicode escapes:** Truncated sequences like `\uD83D` are now reported as  
  `UnexpectedEof` instead of `LoneSurrogate`.  
  This aligns with [RFC 8259](https://www.rfc-editor.org/rfc/rfc8259), `serde_json`,  
  and Go’s `encoding/json`.  
  Example:
  ```rust
  let mut iter = unescape(r"\uD83D");
  let err = iter.next().unwrap().unwrap_err();
  assert!(matches!(err.kind(), UnescapeErrorKind::UnexpectedEof));
````

### Notes

* This changes the exact `UnescapeErrorKind` for truncated surrogate escapes.
  While technically observable, it corrects the behavior to match the JSON spec
  and is therefore treated as a bug fix rather than a breaking change.

---

## \[0.1.0] - 2025-09-18

### Added

* Initial release of streaming JSON string escaping/unescaping.
* Iterator-based API with zero-copy slices.