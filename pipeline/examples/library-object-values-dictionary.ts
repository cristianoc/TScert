// The generic `Object.values<T>` and `Object.entries<T>`, which TypeScript
// selects for a dictionary, read values at `T`: every own string key of a
// dictionary holds one.
function total(d: { readonly [k: string]: number }): number {
  const xs: number[] = Object.values(d);
  const ps: [string, number][] = Object.entries(d);
  return xs.length + ps.length;
}
