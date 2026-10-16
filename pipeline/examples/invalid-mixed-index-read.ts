// A named required field does not make every runtime string key present.
function assumeMixedPresent(
  x: { readonly ready: boolean; readonly [key: string]: boolean },
  key: number,
): boolean {
  return x[key];
}
