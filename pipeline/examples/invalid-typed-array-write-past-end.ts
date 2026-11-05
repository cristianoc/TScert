// A write past the end of a view writes no element, and the read after it
// is `undefined` (run under Node), which TypeScript, narrowing the element
// by the write, types as a number: refused as a number.
export function written(): number {
  const ends = new Int32Array(0);
  ends[0] = 1;
  return ends[0];
}
