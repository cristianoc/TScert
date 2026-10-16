// A callback writing a `Map` it captures: `set` changes the collection, so it
// states no heap preservation, `map` takes its unrestricted overload, and
// the result is sparse. The write shows: the map holds each name afterwards.
export function seen(names: string[], counts: Map<string, number>): string[] {
  return names.map((name) => {
    counts.set(name, (counts.get(name) ?? 0) + 1);
    return name;
  });
}
