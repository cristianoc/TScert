// A read at `n.toString()` of a number `n` is the read at `n`: the standard
// `Number.prototype.toString` of no argument spells the key `o[n]` converts
// `n` to, a canonical numeric key no member of `Object.prototype` is under.
// ReScript compiles `Dict.get(d, Int.toString(k))` to this read.
export function cached(
  cache: { [id: string]: undefined | number },
  k: number,
): undefined | number {
  return cache[k.toString()];
}
export function readonlyRead(
  cache: { readonly [id: string]: boolean },
  k: number,
): boolean | undefined {
  return cache[(k + 1).toString()];
}
