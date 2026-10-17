// A limit whose `ToUint32` is 0 gives no elements: `split(",", 0)` and
// `split(",", 4294967296)` are `[]`, so element 0 may be undefined.
export function first(text: string, limit: number): string {
  return text.split(",", limit)[0];
}

// The same separator without a limit is non-empty: the form is stated, and
// the call passing a limit does not take it.
export function other(text: string): string {
  return text.split(",")[0];
}
