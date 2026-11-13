// A module whose top-level code calls `jumped`, a function the gate refuses
// (a `debugger` statement): its top-level code is left out with `jumped`,
// and `kept`, which reads neither, is kept.
function jumped(x: number): number {
  // `debugger` is outside the fragment:
  debugger;
  return x;
  // the gate refuses the function at it.
}
export function kept(x: number): number {
  return x + 1;
}
export const start: number = jumped(0);
