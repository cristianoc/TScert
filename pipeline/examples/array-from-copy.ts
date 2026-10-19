// `Array.from` of an array copies it through the host's iterator, within
// the empty footprint: a `map` calling it stays dense.
export function copies(rows: (readonly number[])[]): number[][] {
  return rows.map((r) => Array.from(r));
}
