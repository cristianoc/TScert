// A script: its top-level function is a property of the global object, which
// other scripts may write. The pipeline assumes only the file writes its
// top-level bindings (DESIGN, Trust surface), so `g.call` is the standard
// method and `probe` verifies; a script giving `g` an own `call` property
// through the global object is what the assumption excludes.
function g(): number {
  return 1;
}

function probe(h: () => void): number {
  h();
  return g.call(undefined);
}
