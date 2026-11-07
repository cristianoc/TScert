// A loop reading up to and including the length: its last read, `b[i]!` at
// `i === b.length`, is `undefined` at `number`, which `x` returns (run under
// Node: `last(new Uint8Array(2))` is `undefined`).
export function last(b: Uint8Array): number {
  let x = 0;
  for (let i = 0; i <= b.length; i++) x = b[i]!;
  return x;
}
