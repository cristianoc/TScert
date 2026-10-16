// The caller is correct at the callee's signature; the callee is not, and
// its own obligation fails.
function broken(x: boolean): boolean {
  return null;
}
export function caller(x: boolean): boolean {
  return broken(x);
}
