// A function literal calling a member its receiver dispatches on by shape
// (`x.toString()` on `string | number`, on a value tested as a function)
// is stated at the effect of the lowered call's every arm, the object arm
// a call of an unknown callee.
// Census functions:
// family-activation.mts#checkedGuards.
export function matches(text: string, n: number): boolean {
  const runs = (value: unknown, t: string): boolean =>
    typeof value === "function" && value.toString() === t;
  const shown = (x: string | number): string => x.toString();
  return runs(text, text) || shown(n) === text;
}
