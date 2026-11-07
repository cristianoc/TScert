// A write at a key typed as a union of numeric literals, with no guard: the
// write may fall past the length and add an own property no array owns (run
// under Node: `set([], 1, 0)` gives `[1 empty, 0]` at `number[]`).
export function set(xs: number[], k: 0 | 1, v: number): void {
  xs[k] = v;
}
