// Release-profile primitive examples. Public bigint arguments wrap to i64.
pub fn identity(x: i64) -> i64 { x }
pub fn product(x: i64, y: i64) -> i64 { x * y }
pub fn quotient(x: i64, y: i64) -> i64 { x / y }
pub fn remainder(x: i64, y: i64) -> i64 { x % y }
pub fn negate(x: i64) -> i64 { -x }
