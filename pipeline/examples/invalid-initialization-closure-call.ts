// A module constant holding a closure, called by a step before `LIMIT` holds
// its value: the call runs the closure's code, which reads `LIMIT` there, a
// `ReferenceError` the order check refuses.
const twice = (n: number): number => clamp(n) * 2;

function clamp(n: number): number {
  return n > LIMIT ? LIMIT : n;
}

const early = twice(1);

const LIMIT = 10;

export function scaled(n: number): number {
  return twice(n) + early;
}
