// An array literal at a binder bounded by a union with one tuple arm of its
// length is that tuple, as TypeScript's contextual type makes it one, and
// the binder is inferred at it: `pair([1, 2])` is `[number, number]`.
type Pair = [number, number];

function pair<S extends Pair | string>(values: S): S {
  return values;
}

export function first(): number {
  const result = pair([1, 2]);
  const head: number = result[0];
  return head;
}
