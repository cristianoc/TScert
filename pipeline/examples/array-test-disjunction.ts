// Two `Array.isArray` tests joined by `||`: where both fail to fail, each
// operand is its array arm, and a union declaration's array arm stays its
// own, a parsed array of parsed data, whose `map` is dense.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function lengths(
  exprs: number[] | string,
  conts: number[] | string,
): number {
  if (!Array.isArray(exprs) || !Array.isArray(conts)) throw Error("not arrays");
  return exprs.length + conts.length;
}
export function pairs(o: { [key: string]: Json }): number[] {
  const exprs = o.exprs,
    conts = o.conts;
  if (
    !Array.isArray(exprs) ||
    !Array.isArray(conts) ||
    exprs.length !== conts.length
  )
    throw Error("not pairs");
  return exprs.map((e: Json) => (typeof e === "number" ? e : conts.length));
}
