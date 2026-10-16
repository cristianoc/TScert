// A module constant holding a closure, created before a constant the code
// it calls reads: creating the closure runs none of that code, and nothing
// calls it before `LIMIT` holds its value. The initialization-order check
// counts every name a step mentions, a closure body's included, as reached.
const twice = (n: number): number => clamp(n) * 2;

function clamp(n: number): number {
  return n > LIMIT ? LIMIT : n;
}

const LIMIT = 10;

export function scaled(n: number): number {
  return twice(n);
}
