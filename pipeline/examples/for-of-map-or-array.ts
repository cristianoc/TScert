// A `for...of` over a union of host kinds: a `Map` or an empty array, a
// `Set` or an array. The loop steps the union's iteration, which steps the
// value as its kind's intrinsic does and yields the union of their elements.
// Stands for the loop over a guard's promises in `collect`
// (declaration-graph.mts).
export function promised(
  m: Map<string, Map<string, number>>,
  k: string,
): number {
  let n = 0;
  for (const [name, value] of m.get(k) ?? []) n += name.length + value;
  return n;
}

export function letters(
  s: Set<string>,
  xs: readonly string[],
  c: boolean,
): number {
  let n = 0;
  for (const w of c ? s : xs) n += w.length;
  return n;
}

export function lastOf(
  m: Map<string, number>,
  xs: readonly number[],
  c: boolean,
): number {
  let n = 0;
  for (const v of c ? xs : m.values()) n = v;
  return n;
}
