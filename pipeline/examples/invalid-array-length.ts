// `new Array(n)` makes an array of length `n` with no elements: holes,
// which number[] forbids. A length constructor with a hole-admitting element
// type is not implemented; the overlay reads `new Array` with no argument only.
function holes(n: number): number[] {
  return new Array(n);
}
