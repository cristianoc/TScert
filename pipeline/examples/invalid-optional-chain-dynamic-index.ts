// A read at a `number` key in an optional chain over a present array is
// `undefined` past its end: the chain reads through `%ElementAt%`, at the
// element type or `undefined`, so neither return meets `string`.
export function at(xs: readonly string[], i: number): string {
  return xs?.[i];
}

export function argAt(o: { args: readonly string[] }, i: number): string {
  return o?.args[i];
}
