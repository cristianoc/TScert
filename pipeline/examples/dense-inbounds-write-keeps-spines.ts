// An in-bounds write on a `Dense<number[]>` (`i < xs.length`) overwrites an
// existing cell and leaves every array spine unchanged (`spines: "keep"`).
function bump(
  xs: Dense<number[]>,
  i: number,
): Modifies<{ values: "any" }, void> {
  if ((i & 0x7fffffff) !== i || i >= xs.length) throw new RangeError("index");
  xs[i] = 1;
}

/**
 * @requires ys.length === zs.length && safeInteger(i) && 0 <= i && i < ys.length
 */
export function bumpAndRead(
  ys: Dense<number[]>,
  zs: number[],
  i: number,
): number {
  bump(ys, i);
  return zs[i]!;
}
