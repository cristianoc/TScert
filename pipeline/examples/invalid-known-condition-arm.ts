// The disjunction `(c && x) || !c` holds where `c` and `x` are both true,
// so its arm learns nothing of `o.v` there: the assertion is refused, and
// `len(true, true, {})` throws a TypeError under Node.
type O = { readonly v?: string };

export function len(c: boolean, x: boolean, o: O): number {
  if ((c && x) || !c) return o.v!.length;
  return 0;
}
