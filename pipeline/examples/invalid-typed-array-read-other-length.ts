// A read of `b` below the length of another view, `a`: `b[i]!` past `b`'s
// end is `undefined` at `number`, which `x` returns (run under Node:
// `across(new Uint8Array(3), new Uint8Array(1))` is `undefined`).
export function across(a: Uint8Array, b: Uint8Array): number {
  let x = 0;
  for (let i = 0; i < a.length; i++) x = b[i]!;
  return x;
}
