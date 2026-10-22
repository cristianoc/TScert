// A closure wider than the element mapped over an array whose elements admit
// `undefined`, which may hold holes: `map` skips a hole and leaves one in its
// result, read as `undefined`, though the closure never returns it.
type F = { k: "f"; n: number };
type A = { k: "a"; s: string };
type T = A | F;

export function wrong(calls: (F | undefined)[]): string[] {
  const name = (t: T | undefined): string => (t === undefined ? "" : t.k);
  return calls.map(name);
}
