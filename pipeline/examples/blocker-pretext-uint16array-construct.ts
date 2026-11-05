// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-breaks.ts#hasProperty, line-breaks.ts#unpackClassRuns.
// `new Uint16Array(n)`, through the global's reviewed entry: only
// constructed, at a length or an array of numbers.
export function runs(n: number): number {
  const out = new Uint16Array(n);
  return out.length;
}
