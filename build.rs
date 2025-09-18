use std::env;
use std::process::Command;

fn main() {
    // Get the rustc version
    let rustc = env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
    let output = Command::new(rustc).arg("--version").output().unwrap();
    let version = String::from_utf8(output.stdout).unwrap();

    // Check if the version string contains "-nightly"
    if version.contains("-nightly") {
        // If it does, enable the "simd" feature for the library compilation.
        println!("cargo:rustc-cfg=feature=\"simd\"");
    }
}
