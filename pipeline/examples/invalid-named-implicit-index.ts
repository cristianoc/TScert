// A named type permits extra keys with values outside a dictionary's contract.
export function asDictionary(x: { readonly a: number }): {
  readonly [key: string]: number;
} {
  return x;
}
