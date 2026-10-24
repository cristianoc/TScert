// A guard whose promise is `x is never`, which shrinks the array it is
// handed and returns `false`, called in a `map` callback: the call's term is
// a Boolean, a value, so the call returns normally and the callback is
// bounded by the guard's footprint. The result may hold holes and is not
// `number[]` (run under Node: `map` skips the index the guard removed).
function isNever(xs: number[], x: number): x is never {
  xs.pop();
  return false;
}

export function wrong(xs: number[]): number[] {
  const r: number[] = xs.map((x) => (isNever(xs, x) ? 0 : x));
  return r;
}
