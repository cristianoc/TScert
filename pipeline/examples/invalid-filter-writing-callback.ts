// A `filter` callback writing an array it captures: `filter` takes its
// unrestricted signature, so the `map` callback calling it states no heap
// preservation, `map` takes its unrestricted overload, and the result is
// sparse. The write shows: `kept` holds every word afterwards.
export function words(lines: string[], kept: string[]): string[][] {
  return lines.map((l) => l.split(" ").filter((w) => {
    kept.push(w);
    return w !== "";
  }));
}
