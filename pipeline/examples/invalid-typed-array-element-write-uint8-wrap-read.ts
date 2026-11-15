// A Uint8Array write of 300 stores its conversion, 44 (run under Node:
// `past(new Array(300).fill(1), new Uint8Array(1))` reads `widths[-212]`,
// `undefined` at `number`): the element read back is not the value written.

/** @requires 300 <= widths.length */
export function past(widths: number[], bytes: Uint8Array): number {
  if (bytes.length < 1) return 0;
  bytes[0] = 300;
  return widths[bytes[0]! - 256]!;
}
