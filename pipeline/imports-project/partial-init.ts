// A module whose top-level code calls `jumped`, a function the gate refuses
// (a function declaration after its `return`): the module is refused as a
// whole, `kept` with it.
function jumped(x: number): number {
  return inner(x);
  function inner(y: number): number {
    return y;
  }
}
export function kept(x: number): number {
  return x + 1;
}
export const start: number = jumped(0);
