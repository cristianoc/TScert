// `isPositive` keeps its promise: a `true` result leaves its argument a
// number. TypeScript also narrows the `false` outcome, to the arms outside
// `number`, which the promise does not state: `-1` is a number it answers
// `false` for, and `shout(-1)` calls `toUpperCase` on it.
export function isPositive(x: unknown): x is number {
  return typeof x === "number" && x > 0;
}

export function shout(v: number | string): string {
  if (isPositive(v)) return "positive";
  return v.toUpperCase();
}
