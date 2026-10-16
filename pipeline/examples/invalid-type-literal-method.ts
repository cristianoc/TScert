// A method signature is received by its object: read off it, it is not a
// function value another call may run without it.
export function detach(o: { m(): number }): () => number {
  return o.m;
}
