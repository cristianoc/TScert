// A user guard on a dictionary member refines the member reread, an
// object-valued result included: each guard's body keeps the heap, so a test
// of a member's read, and a test of a second member after it, is one of the
// value the reread gives (PROGRAM-TYPING.md, "A call that keeps the heap").
// Census functions:
// claim-text.mts#atomText, claim-text.mts#bareAtomText,
// claim-text.mts#printType, claim-text.mts#restElement,
// claim-text.mts#setLiterals, claim-text.mts#typeText, claim.mts#atom,
// claim.mts#decodeClaimType, diagnostic.mts#readDiagnostic.
type Json = null | boolean | number | string | readonly Json[] | Dict;
type Dict = { readonly [key: string]: Json };
function isList(value: Json | undefined): value is readonly Json[] {
  return Array.isArray(value);
}
function isObject(value: Json | undefined): value is Dict {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
export function use(x: Dict): number {
  if (isList(x.args)) return x.args.length;
  return 0;
}
export function both(atom: Dict): number {
  if (
    (atom.a === "array" || atom.a === "store") &&
    isList(atom.required) &&
    isList(atom.optional)
  )
    return atom.required.length + atom.optional.length;
  return 0;
}
export function index(atom: Dict): Dict | null {
  return isObject(atom.indexSignature) ? atom.indexSignature : null;
}
