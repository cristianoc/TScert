// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#getFontKanaKerning.
// Refusal: gate: the global Float64Array is declared in
// typescript/lib/lib.es5.d.ts (library), an origin no reviewed entry
// admits.
// `new Float64Array(n)`: the global `Float64Array` has no reviewed entry.
export function kerning(n: number): number {
  const out = new Float64Array(n);
  return out.length;
}
