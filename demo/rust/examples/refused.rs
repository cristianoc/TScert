// Refused: in the model `x + 1` is a number (`x` is an `i32`), and the
// result must be a bigint (`i64`). rustc rejects this function too.
fn widen(x: i32) -> i64 {
    x + 1
}
