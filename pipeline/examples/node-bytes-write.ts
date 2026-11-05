// A write through a view of bytes at a number is `%ByteSet%`'s: it converts
// its value by ToNumber, which runs no code on a number, and keeps it modulo
// 256 (run under Node: 300 reads back as 44). The element read back is a
// number, or `undefined` past the end.
export function write(bytes: Buffer, value: number): number {
  bytes[0] = value;
  return bytes[0] ?? -1;
}
