// A runtime string may name an absent property.
function assumeDynamicPresent(
  x: { readonly [key: string]: boolean },
  key: number,
): boolean {
  return x[key];
}
