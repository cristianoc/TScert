// `Modifies<{ values: "any"; views: "grow" }, void>` writes typed-array view
// bytes while keeping every ordinary array spine's length unchanged.
function writeFirst(
  v: Uint8Array,
  x: number,
): Modifies<{ values: "any"; views: "grow" }, void> {
  if (v.length > 0) v[0] = x;
}

/**
 * @requires xs.length === ys.length && safeInteger(i) && 0 <= i && i < xs.length
 */
export function writeViewAndRead(
  v: Uint8Array,
  xs: number[],
  ys: number[],
  i: number,
): number {
  writeFirst(v, 7);
  return xs[i]! + ys[i]!;
}
