// A `for...of` binding destructured: each iteration binds the element, then
// the pattern reads it, before the body. An array of pairs, a `Map`'s
// entries, and an object pattern with a default.
export function joined(entries: [string, string][]): Map<string, string> {
  const out = new Map<string, string>();
  for (const [key, value] of entries)
    out.set(key, out.has(key) ? `${out.get(key)} ${value}` : value);
  return out;
}

export function total(counts: Map<string, number>): number {
  let sum = 0;
  for (const [, n] of counts) sum += n;
  return sum;
}

type Item = { name: string; size?: number };
export function sizes(items: Item[]): number {
  let sum = 0;
  for (const { size = 1 } of items) sum += size;
  return sum;
}
