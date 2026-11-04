// An overload its implementation's code does not meet: at a string, `pick`
// returns the string where the overload promises a number. TypeScript checks
// the body at the implementation's own signature alone (run under Node:
// `fixed()` throws a TypeError, `toFixed` of a string).
export function pick(x: number): number;
export function pick(x: string): number;
export function pick(x: number | string): number | string {
  return x;
}
export function fixed(): string {
  return pick("a").toFixed(1);
}
