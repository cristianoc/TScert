// Results of a callback of no stated effect collected by a loop that pushes
// each onto a fresh array, then read as a readable array: the form
// `intrinsics.mts#iterationIntrinsic`, `#intrinsics` and
// `host-families.mts#familyTable` use (SOURCE-REWRITES.md, "Results of an
// unrestricted callback collected by a loop"). `xs.map(read)` with such a
// callback may leave holes (`blocker-round-inferred-map-result`); each push
// appends a present element.
type Part = { name: string; size: number };

export function parts(names: readonly string[], read: (name: string, suffix: string) => Part): number {
  const collected: Part[] = [];
  for (const name of names) collected.push(read(name, names.length > 1 ? String(collected.length) : ""));
  const only = collected.length === 1 ? collected[0] : undefined;
  const total = only ? only.size : collected.map(p => p.size).reduce((a, b) => a + b, 0);
  return total;
}
