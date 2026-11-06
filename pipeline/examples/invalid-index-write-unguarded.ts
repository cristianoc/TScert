// No guard: an index past the length leaves holes, read as `undefined` at
// `number` (run under Node).
export function wrong(xs: number[], k: number, v: number): number[] {
  xs[k] = v;
  return xs;
}
