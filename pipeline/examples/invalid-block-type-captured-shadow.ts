// `Both`'s own `T` is `number`, its `outer.v` the enclosing `T`: a number
// stored at `outer.v` is no `T`, and the result holds it where the contract
// states the caller's `T`.
function swap<T>(value: T, n: number): T {
  type Outer = { v: T };
  type Both<T> = { outer: Outer; own: T };
  // @ts-expect-error -- `outer.v` is the enclosing `T`
  const both: Both<number> = { outer: { v: n }, own: n };
  return value === value ? both.outer.v : value;
}
