// TypeScript accepts this under --strict, but an absent key reads undefined.
function assumePresent(x: { readonly [key: string]: boolean }): boolean {
  return x["missing"];
}
