// A statement on an overload: a declaration's unit is certified at one
// signature, so no check would establish it.
export function pick(xs: number[], flag: true): Modifies<{}, number>;
export function pick(xs: number[], flag: false): number;
export function pick(xs: number[], flag: boolean): number {
  if (!flag) xs.pop();
  return 0;
}
