// A file-level function handed to a caller's function may be given an own
// `call` property there, which `g.call` then runs.
function g(): number {
  return 1;
}

function probe(h: (f: () => number) => void): number {
  h(g);
  return g.call(undefined);
}
