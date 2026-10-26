// A type not stating `cause` is open at it: the options may own a getter
// there, which `Error` runs through `[[Get]]`, client code that may shrink
// the array `map` visits. Refused at the options.
export function wrong(xs: string[], options: { reason: string }): string[] {
  return xs.map((x) => Error(x, options).message);
}
