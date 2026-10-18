// A module whose functions the certified-import examples import. The gate
// admits all of it, so each import is read at the footprint its unit's own
// certificate states.
export function twice(x: number): number {
  return x + x;
}
function describe(n: number): string {
  return n > 0 ? "positive" : "other";
}
export function label(n: number): string {
  return describe(n);
}
export function tally(seen: number[], x: number): number {
  seen.push(x);
  return seen.length;
}
export function drop(xs: number[]): number {
  xs.pop();
  return 0;
}
