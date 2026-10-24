// Statements on overloaded declarations (`invalid-stated-overload-value-import`,
// `invalid-stated-one-overload-value-import`): a declaration's unit is
// certified at one signature, so no run checks a statement on an overload or
// on the implementation beside one.
export function pick(
  xs: number[],
  flag: true,
): Within<{ value: "keep"; store: "keep" }, number>;
export function pick(xs: number[], flag: false): number;
export function pick(xs: number[], flag: boolean): number {
  if (!flag) xs.pop();
  return 0;
}

export function only(xs: number[]): number;
export function only(
  xs: number[],
): Within<{ value: "keep"; store: "keep" }, number> {
  xs.pop();
  return 0;
}
