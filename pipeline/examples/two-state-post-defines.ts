// Rule Call through one entry value: `grow`'s postcondition relates
// `ys.length` after the call and the value `r` it returns through
// `old(ys.length)`, which the post, holding, defines. Its two equalities
// compose into `ys.length === r + 1`, and `bs[ys.length - r - 1]` reads
// index 0.

/**
 * @requires 0 <= ys.length && ys.length <= 1000
 * @ensures safeInteger(result) && ys.length === old(ys.length) + 1 && result === old(ys.length)
 */
function grow(ys: number[]): Modifies<{ values: "any"; stores: "grow" }, number> {
  const n = ys.length;
  ys.push(0);
  return n;
}

type Box = { /** @stable */ readonly xs: number[] };

/** @requires 0 <= o.xs.length && o.xs.length <= 1000 && bs.length === 1 */
export function first(o: Box, bs: number[]): number {
  const ys = o.xs;
  const r = grow(ys);
  return bs[ys.length - r - 1]!;
}
