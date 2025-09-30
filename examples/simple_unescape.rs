//! Basic unescaping from a string slice into a `String`.

use json_escape::unescape;
use std::borrow::Cow;

fn main() {
    let input = r#"Emoji: \uD83D\uDE00 and a tab\t!"#;
    let expected = "Emoji: 😀 and a tab\t!";

    // `unescape` returns an iterator over Result<&[u8], _>.
    // `.decode_utf8()` collects and validates into a `Cow<str>`.
    let decoded: Cow<str> = unescape(input).decode_utf8().unwrap();

    assert_eq!(decoded, expected);
    println!("Unescaped string: {}", decoded);
}
