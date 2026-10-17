// A `filter` callback pushing onto an array it captures, inside a `map`
// callback: `filter` is within its callback's footprint,
// `{value: any, store: grow}`, so the `map` callback is too, which keeps the
// mapped array's dense prefixes, and the result is dense. The write shows:
// `kept` holds every word afterwards.
export function words(lines: string[], kept: string[]): string[][] {
  return lines.map((l) =>
    l.split(" ").filter((w) => {
      kept.push(w);
      return w !== "";
    }),
  );
}
