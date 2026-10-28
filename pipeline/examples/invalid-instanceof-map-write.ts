// `instanceof Map` states no element contract to write by: a map the caller
// holds as a `Map<string, number>` would hold a string after the write
// (run under Node). The test promises the map's reading view, which has no
// `set`, so the write is refused.
export function overwrite(value: unknown): void {
  if (value instanceof Map) value.set("k", "text");
}
export function caller(): number | undefined {
  const counts = new Map<string, number>([["k", 1]]);
  overwrite(counts);
  return counts.get("k");
}
