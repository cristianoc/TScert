// A conditional map/flatMap result in a mutable local used as a filter receiver.
// Census functions:
// fragment-parse.mts#parseFile
// fragment-parse.mts#parseFragment
// fragment-parse.mts#lowerModule
// fragment-parse.mts#lowerModuleText
// fragment-parse.mts#parseModules
// fragment-parse.mts#lowerFile
type Item = { value: number };
export function select(
  xs: number[],
  partial: boolean,
  read: (x: number) => Item,
): Item[] {
  let lowered = partial
    ? xs.map((x) => ({ source: x, item: read(x) }))
    : xs.flatMap((x) => [{ source: x, item: read(x) }]);
  for (;;) {
    const kept = lowered.filter(({ item }) => item.value > 0);
    const changed = kept.length < lowered.length;
    lowered = kept;
    if (!changed) return kept.map(({ item }) => item);
  }
}
