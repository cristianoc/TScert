// Allowing `i === xs.length` (`i > xs.length` instead of `i >= xs.length`)
// appends a new element and grows the array spine, violating `spines: "keep"`.
function append(
  xs: Dense<number[]>,
  i: number,
): Modifies<{ values: "any" }, void> {
  if ((i & 0x7fffffff) !== i || i > xs.length) throw new RangeError("index");
  xs[i] = 1;
}

/**
 * @requires ys.length === zs.length
 */
export function appendAndRead(ys: Dense<number[]>, zs: number[]): number {
  append(ys, ys.length);
  return zs[ys.length - 1]! + 1;
}
