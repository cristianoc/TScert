// Writes that keep an array dense: into a required position, or at an index
// no greater than the required length, which is in bounds or appends.
function setFirst(xs: number[], n: number): number[] {
  xs[0] = n;
  return xs;
}

function setSecond(pair: [number, number], n: number): [number, number] {
  pair[1] = n;
  return pair;
}
