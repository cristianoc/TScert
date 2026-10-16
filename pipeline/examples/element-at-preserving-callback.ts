// Callbacks reading an array at a `number` key, `%ElementAt%`, which runs no
// code and writes nothing: the read states heap preservation, so each
// callback does and `map`'s result is dense.
export function previous(ts: string[]): (string | undefined)[] {
  return ts.map((_, i) => ts[i - 1]);
}

const at = (ts: readonly string[], k: number): boolean => ts[k] === "=";
export function marks(ts: string[]): boolean[] {
  return ts.map((_, i) => at(ts, i + 1));
}
