// The tuple is `[number, number]`: its first position is no `1`.
type Pair = [number, number];

function pair<S extends Pair | string>(values: S): S {
  return values;
}

export function first(): 1 {
  const result = pair([1, 2]);
  return result[0];
}
