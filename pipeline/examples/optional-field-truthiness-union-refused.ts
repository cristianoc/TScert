// A truthy read of a field one arm of a union leaves optional and another
// requires: TypeScript reads the field in the branch at its type; here the
// argument keeps `undefined`.
type Required = { readonly kind: 1; readonly m: { x: number } };
type Optional = { readonly kind: 2; readonly m?: { x: number } };

export function inner(
  found: Required | Optional,
  f: (n: { x: number }) => number,
): number {
  if (found.m) return f(found.m);
  return 0;
}
