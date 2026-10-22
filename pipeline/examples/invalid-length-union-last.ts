// A union of an array and a record with a `length` and a numeric index
// signature: the record's `length` names no key it owns, and the read is
// `undefined`.
export function last(
  xs:
    | readonly string[]
    | { readonly length: number; readonly [k: number]: string },
): string {
  return xs[xs.length - 1];
}
