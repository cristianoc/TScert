// Two maps resolving declarations and serializing locations, with a
// `resolve` field that states no effect: it may shrink the declarations
// array while the first map runs, which leaves a hole in its result and in
// the second map's, so the returned string[] reads undefined. Under Node, a
// resolve that pops the array gives a result of length 2 whose index 1 is
// absent. The census function type-probe.mts#makeProbe uses compiler
// declarations, whose host contract states resolve's effect
// (blocker-gap-round-locations-map).
type Declaration = { resolve: () => { file: string; offset: number } | null };
type Symbol = { declarations?: readonly Declaration[] };
export function locations(symbol: Symbol | undefined): string[] {
  const where = (node: { file: string; offset: number }): unknown => ({
    file: node.file,
    offset: node.offset,
  });
  return (symbol?.declarations ?? [])
    .map((d) => {
      const node = d.resolve();
      return node ? where(node) : null;
    })
    .map((d) => JSON.stringify(d));
}
