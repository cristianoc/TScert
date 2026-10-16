// A rest parameter of a tuple contract collects the further actuals too, so
// its function meets only its own positions.
function pair(...xs: [number]): number {
  return xs.length;
}
export function widen(): (a: number, b: string) => number {
  return pair;
}
