// A crate exported to JavaScript by wasm-bindgen.
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[wasm_bindgen]
pub fn scale(x: i64, k: i64) -> i64 {
    if k == 0 { x } else { x * k }
}

#[wasm_bindgen]
pub fn greet(name: &str) -> String {
    "hello, ".to_string() + name
}

#[wasm_bindgen]
pub fn next_id() -> i64 {
    42
}

#[wasm_bindgen]
pub fn identity(x: i64) -> i64 { x }

#[wasm_bindgen]
pub fn quotient(x: i64, y: i64) -> i64 { x / y }

#[wasm_bindgen]
pub fn remainder(x: i64, y: i64) -> i64 { x % y }

#[wasm_bindgen]
pub fn negate(x: i64) -> i64 { -x }
