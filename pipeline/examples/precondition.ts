// Preconditions (`@requires`): a function assumes its clause, and
// every call establishes it. `at` reads `xs[i]!` with no check; `sum` calls it
// in a loop below the length; `plus` assumes a safe integer, which a literal is.

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
function at(xs: number[], i: number): number {
  return xs[i]!;
}

/** @requires safeInteger(i) */
function plus(i: number): number {
  return i + 1;
}

export function sum(xs: number[]): number {
  let s = plus(0);
  for (let j = 0; j < xs.length; j++) s = s + at(xs, j);
  return s;
}
