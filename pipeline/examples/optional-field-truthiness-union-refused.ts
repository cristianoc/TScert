// A truthy read of a field one arm of a union leaves optional and another
// requires: the witness in the branch holds the field's non-undefined value.
type Required = { readonly kind: 1; readonly m: { x: number } };
type Optional = { readonly kind: 2; readonly m?: { x: number } };

export function inner(
  found: Required | Optional,
  f: (n: { x: number }) => number,
): number {
  if (found.m) return f(found.m);
  return 0;
}
