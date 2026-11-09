// Builders stating a fresh result and no frame: each returns the array a
// native call allocates, so each unit certifies `Fresh<number[]>`. `same`
// states none: it returns the array it is handed (a control forges a fresh
// statement onto it).
export function copy(xs: readonly number[]): Fresh<number[]> {
  return xs.slice();
}

export function doubled(xs: readonly number[]): Fresh<number[]> {
  const out = xs.map((x) => x * 2);
  return out;
}

export function same(xs: number[]): number[] {
  return xs;
}
