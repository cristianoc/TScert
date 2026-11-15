// A write through a view of bytes at a number is `%ByteSet%`'s: it converts
// its value by ToNumber, which runs no code on a number, and stores the
// format's conversion of it (run under Node: 300 reads back as 44, -1 as
// 255 and NaN as 0), and at a number that is no valid index it changes no
// element (run under Node: a write at 5 of a view of length 1 leaves its
// element). The element read back is a number, or `undefined` past the end.
export function write(bytes: Buffer, value: number): number {
  bytes[0] = value;
  return bytes[0] ?? -1;
}

export function writeAt(bytes: Buffer, index: number, value: number): number {
  bytes[index] = value;
  return bytes[0] ?? -1;
}
