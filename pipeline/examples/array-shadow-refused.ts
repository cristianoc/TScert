// An array owns no key its prototype provides, so `xs.map` is always
// `Array.prototype.map`: an array with an own `map` field is no array type,
// and its intersection is refused rather than verified vacuously.
export function shadow(xs: number[] & { map: number }): number {
  return xs.length;
}
