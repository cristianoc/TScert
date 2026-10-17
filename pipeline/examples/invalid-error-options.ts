// `Error`'s options are read for `cause` through `[[Get]]`, which runs a
// getter: client code that may shrink the array `map` visits. The call is
// read with the message only.
export function wrong(xs: string[], options: { cause: unknown }): string[] {
  return xs.map((x) => Error(x, options).message);
}
