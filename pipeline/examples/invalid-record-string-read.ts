// `Record<string, number>` is a string index: a key it does not own reads
// `undefined`, so a read at an arbitrary key is not a number. TypeScript
// accepts this without `noUncheckedIndexedAccess`; it is unsound.
function get(r: Record<string, number>, k: number): number {
  return r[k];
}
