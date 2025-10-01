//! Demonstrates streaming unescape from a file using `UnescapeStream`.

use json_escape::{stream::UnescapeStream, token::UnescapedToken};
use std::fs::File;
use std::io::{self, Read};
use std::path::PathBuf;

fn main() -> io::Result<()> {
    let file_path = get_file_path();

    // Example input file: contains escaped JSON string like
    //   "Hello, \\\"stream\\\"! \\uD83D\\uDE00 Goodbye!"
    let mut file = File::open(file_path)
        .expect("Failed to open tests/data/escaped.txt. Make sure the file exists.");

    let mut unescaper = UnescapeStream::new();
    let mut result = String::new();

    // Fixed-size buffer
    let mut buf = [0u8; 8];

    loop {
        let n = file.read(&mut buf)?;
        if n == 0 {
            break; // EOF
        }

        let (boundary, tokens) = unescaper.try_unescape_next(&buf[..n]).unwrap();

        if let Some(ch) = boundary {
            result.push(ch);
        }

        for token in tokens {
            match token.unwrap() {
                UnescapedToken::Literal(bytes) => {
                    result.push_str(std::str::from_utf8(bytes).unwrap())
                }
                UnescapedToken::Unescaped(c) => result.push(c),
            }
        }
    }

    // Finalize stream: ensures no incomplete escape left over
    unescaper.finish().unwrap();

    println!("Unescaped file content:\n{}", result);
    Ok(())
}

fn get_file_path() -> PathBuf {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let mut file_path = PathBuf::from(manifest_dir);
    file_path.push("tests/data/escaped.txt");
    file_path
}
