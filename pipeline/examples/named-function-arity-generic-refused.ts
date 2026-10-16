// A generic module function also discards the actuals past its parameters,
// but its use is read at the instance it names, which has no extension by a
// rest of `unknown`: refused as a gap.
function first<T>(x: T): T {
  return x;
}
function each(f: (x: number, i: number) => number): number {
  return f(1, 2);
}
export function passed(): number {
  return each(first);
}
