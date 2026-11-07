// Each function is a unit of its own; `hypot2` and `origin_distance2` read a
// struct, `sign` and `clamp` lower `if` both as statements and as values.

struct Point {
    x: f64,
    y: f64,
}

fn greet(name: &str) -> String {
    "hello ".to_string() + name
}

fn inc(x: i32) -> i32 {
    x + 1
}

fn sign(x: i64) -> i64 {
    if x < 0 {
        return -1;
    }
    if x == 0 { 0 } else { 1 }
}

fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
    let below = x < lo;
    let y = if below { lo } else { x };
    if y > hi { hi } else { y }
}

fn average(a: i64, b: i64) -> i64 {
    let sum = a + b;
    sum / 2
}

fn hypot2(p: Point) -> f64 {
    p.x * p.x + p.y * p.y
}

fn origin_distance2(x: f64, y: f64) -> f64 {
    hypot2(Point { x: x, y: y })
}

fn nonempty(s: &str) -> bool {
    !(s == "")
}
