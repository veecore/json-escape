//! Shows how to use the low-level token API for custom processing.

use json_escape::token::{EscapedToken, UnescapedToken, escape_str, unescape};

fn main() {
    let raw = "Hello, \"world\"!\nThis is a backslash: \\";
    println!("Original: {}", raw);

    // Escape using tokens
    let escaped: String = escape_str(raw)
        .map(|tok| match tok {
            EscapedToken::Literal(s) => s,
            EscapedToken::Escaped(e) => e,
        })
        .collect();

    println!("Escaped: {}", escaped);

    // Unescape back into tokens
    let unescaped: String = unescape(&escaped)
        .map(|res| match res.unwrap() {
            UnescapedToken::Literal(bytes) => std::str::from_utf8(bytes).unwrap().to_owned(),
            UnescapedToken::Unescaped(c) => c.to_string(),
        })
        .collect();

    println!("Round-tripped: {}", unescaped);
}
