// A byte read past the end is `undefined` (run under Node), which
// TypeScript types at the element without `noUncheckedIndexedAccess`:
// refused as a number.
export function last(bytes: Buffer): number {
  return bytes[bytes.length];
}
