// `map` callbacks removing from arrays they allocated: through a constant
// whose code returns `filter`'s fresh result, from `split` and from `map`.
// `shift`, `pop` and `reverse` change only their receiver's store beside
// element contents, and each receiver's store was allocated after the
// callback began, so each callback is within `{value: any, store: keep}`
// and every result is dense.
const parts = (line: string): string[] =>
  line
    .trim()
    .split(/\s{3,}/)
    .filter(Boolean);
const same = (a: string[]): string[] => a;

export function heads(lines: string[]): string[] {
  return lines.map((l) => {
    const rest = parts(l);
    return rest.shift() ?? "";
  });
}

export function lasts(lines: string[]): string[] {
  return lines.map((l) => {
    const cells = l.split(",");
    const copy = cells;
    return copy.pop() ?? "";
  });
}

export function backwards(lines: string[]): string[] {
  return lines.map((l) => {
    const widths = l.split(",").map((c) => c.length);
    widths.reverse();
    return widths.join(",");
  });
}

export function sizes(lines: string[]): number[] {
  return lines.map((l) => same(parts(l)).length);
}
