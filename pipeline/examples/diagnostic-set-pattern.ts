// An array pattern over a Set: the pattern's element read is refused (an
// array pattern needs an array contract). Stands for `parameterIndex` in
// `makeProbe` (type-probe.mts), whose census slice reported `Set`, `Map`
// and the iteration intrinsics unbound after this refusal.
export function only(xs: number[]): number | null {
  const seen = new Set<number>();
  for (const x of xs) seen.add(x);
  const [first] = seen;
  return seen.size === 1 && first !== undefined ? first : null;
}
