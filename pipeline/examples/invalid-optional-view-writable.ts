// A readonly optional field does not cover a writable one, even of the same
// type: the target's contract would permit writes the source's does not.
function read(value: { limit?: number }): number | undefined {
  return value.limit;
}
export function pass(value: { readonly limit?: number }): number | undefined {
  return read(value);
}
