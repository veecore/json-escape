All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),  
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

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