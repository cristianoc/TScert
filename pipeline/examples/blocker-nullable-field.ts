// A user guard on a dictionary member needs to refine the member reread,
// including an object-valued result.
// Census functions:
// claim-text.mts#atomText, claim-text.mts#bareAtomText,
// claim-text.mts#printType, claim-text.mts#restElement,
// claim-text.mts#setLiterals, claim-text.mts#typeText, claim.mts#atom,
// claim.mts#decodeClaimType, diagnostic.mts#readDiagnostic.
type Json = null | boolean | number | string | readonly Json[] | Dict;
type Dict = { readonly [key: string]: Json };
declare function isList(value: Json | undefined): value is readonly Json[];
export function use(x: Dict): number {
  if (isList(x.args)) return x.args.length;
  return 0;
}
