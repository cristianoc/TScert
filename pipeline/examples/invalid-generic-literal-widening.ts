// Nothing expects `wrap(42)` at a literal: it is `{ v: number }`, whose
// writable field holds any number, so its read is no `42`.
function wrap<T>(x: T): { v: T } {
  return { v: x };
}

export function use(): 42 {
  const w = wrap(42);
  return w.v;
}
