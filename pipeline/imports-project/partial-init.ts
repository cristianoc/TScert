// A module whose top-level code calls `jumped`, a function the gate refuses
// (a `debugger` statement): the module is refused as a
// whole, `kept` with it.
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
