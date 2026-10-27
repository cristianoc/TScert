// A write through a view of bytes converts its value by ToNumber and keeps
// it modulo 256 (run under Node: 300 reads back as 44); the stated view is
// readonly, refused.
export function write(bytes: Buffer, value: number): number {
  bytes[0] = value;
  return bytes[0] ?? -1;
}
