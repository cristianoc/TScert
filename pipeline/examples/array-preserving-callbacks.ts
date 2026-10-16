// `filter`, `some`, `every` and `forEach` at a callback preserving the input
// heap preserve it too: beside the callback they read the receiver and
// allocate only `filter`'s result. So a `map` callback calling them, with
// such a callback or with `Boolean` read as a value, preserves the heap, and
// `map`'s result is dense.
export function words(lines: string[]): string[][] {
  return lines.map((l) => l.split(" ").filter((w) => w !== ""));
}

export function nonEmpty(lines: string[]): string[][] {
  return lines.map((l) => l.split(" ").filter(Boolean));
}

export function marks(rows: string[][]): boolean[] {
  return rows.map((r) => r.some((c) => c === "x") && r.every((c) => c.length < 3));
}

export function visited(rows: string[][]): number[] {
  return rows.map((r) => {
    r.forEach((c) => c.length);
    return r.length;
  });
}
