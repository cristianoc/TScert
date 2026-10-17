// A callback filling a `Set` it creates: `new Set()` allocates, the array
// iterator's step writes only its position and `add` the set's internal
// slots, all within `{value: any, store: keep}`, so the result is dense.
export function distinct(xs: readonly (readonly string[])[]): number[] {
  return xs.map((ys: readonly string[]): number => {
    const seen = new Set<string>();
    for (const y of ys) seen.add(y);
    return seen.size;
  });
}
