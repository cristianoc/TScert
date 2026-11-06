// Explicit function captures and calls within a module.
pub fn identity(x: i64) -> i64 { x }
pub fn text(x: &str) -> String { x.to_string() }
pub fn forward(x: i64) -> i64 { identity(x) }
