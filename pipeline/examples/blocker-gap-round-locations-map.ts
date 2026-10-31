// Two maps resolving declarations and serializing locations.
// Census functions:
// type-probe.mts#makeProbe
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
