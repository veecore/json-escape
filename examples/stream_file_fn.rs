//! Demonstrates streaming unescape from a file using `UnescapeStream::unescape_from_fn`.

use json_escape::stream::ReadChunkSource;
use json_escape::{stream::UnescapeStream, token::UnescapedToken};
use std::fs::File;
use std::io;

fn main() -> io::Result<()> {
    let file = File::open("tests/data/escaped.txt")?;
    let mut result = String::new();
    let buf = [0u8; 8]; // streaming buffer

    // Source closure: pulls chunks from file
    let src = ReadChunkSource::new(file, buf);

    // Destination closure: handles tokens
    let mut dst = |token: UnescapedToken<'_>| -> io::Result<()> {
        match token {
            UnescapedToken::Literal(bytes) => result.push_str(std::str::from_utf8(bytes).unwrap()),
            UnescapedToken::Unescaped(c) => result.push(c),
        }
        Ok(())
    };

    // Drive stream: src → unescape → dst
    UnescapeStream::new()
        .unescape_from_source(src, &mut dst)
        .unwrap();

    println!("Driver stream unescaped:\n{}", result);
    Ok(())
}
