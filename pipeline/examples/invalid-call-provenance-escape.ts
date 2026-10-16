// A local function handed to a caller's function may be given an own `call`
// property there, which `g.call` then runs.
function probe(h: (f: () => number) => void): number {
  const g = (): number => 1;
  h(g);
  return g.call(undefined);
}
