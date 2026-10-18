// A key test of a literal key changes no location: a `map` callback testing
// one, directly or through a declaration, keeps the result dense.
type Shape = { kind?: string; size: number };
function hasKind(s: Shape): boolean {
  return "kind" in s;
}
export function kinds(ss: Shape[]): boolean[] {
  return ss.map((s) => "kind" in s && hasKind(s));
}
