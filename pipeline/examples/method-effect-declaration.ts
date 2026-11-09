// Function declarations stating the empty footprint: each unit is certified
// at its statement, whether or not any code calls it, and a `map` callback
// calling one is within it.
function half(n: number): Modifies<{}, number> {
  return n / 2;
}

export function third(n: number): Modifies<{}, number> {
  return n / 3;
}

export function halves(xs: number[]): number[] {
  const r: number[] = xs.map((x) => half(x));
  return r;
}
