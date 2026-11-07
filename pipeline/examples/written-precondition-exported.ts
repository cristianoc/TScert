// A precondition on an exported function: the function is checked assuming
// it, a call in its module establishes it, and a caller outside the analyzed
// sources is trusted to (DESIGN.md, trust surface).

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function at(xs: number[], i: number): number {
  return xs[i]!;
}

export function total(xs: number[]): number {
  let s = 0;
  for (let j = 0; j < xs.length; j++) s = s + at(xs, j);
  return s;
}
