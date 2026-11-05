// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-breaks.ts#hasProperty, line-breaks.ts#unpackClassRuns.
// Refusal: gate: the global Uint16Array is declared in
// typescript/lib/lib.es5.d.ts (library), an origin no reviewed entry
// admits.
// `new Uint16Array(n)`: the global `Uint16Array` has no reviewed entry.
export function runs(n: number): number {
  const out = new Uint16Array(n);
  return out.length;
}
