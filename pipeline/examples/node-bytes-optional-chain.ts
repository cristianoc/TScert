// A byte read at a `number` key in an optional chain is `%ByteAt%` on the
// chain's present view, as outside a chain: the byte at a valid index, else
// `undefined`.
export function byteAt(
  b: Uint8Array | undefined,
  i: number,
): number | undefined {
  return b?.[i];
}
