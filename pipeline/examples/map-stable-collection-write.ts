// A callback writing a `Map` it captures: `set` writes the collection's
// internal slots, within `{value: any, store: keep}`, which keeps the
// mapped array's dense prefixes, so the result is dense. The write shows: the
// map holds each name afterwards.
export function seen(names: string[], counts: Map<string, number>): string[] {
  return names.map((name) => {
    counts.set(name, (counts.get(name) ?? 0) + 1);
    return name;
  });
}
