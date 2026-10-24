// A statement on an overload (`invalid-stated-overload-value-import`): a
// declaration's unit is certified at one signature, so no run checks it.
export function pick(
  xs: number[],
  flag: true,
): Within<{ value: "keep"; store: "keep" }, number>;
export function pick(xs: number[], flag: false): number;
export function pick(xs: number[], flag: boolean): number {
  if (!flag) xs.pop();
  return 0;
}
