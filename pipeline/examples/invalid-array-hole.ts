// A write at index 1 of an array that may be empty would leave a hole at
// index 0, which a dense array cannot have: it is refused. Use `push`.
function setSecond(xs: number[], n: number): number[] {
  xs[1] = n;
  return xs;
}
