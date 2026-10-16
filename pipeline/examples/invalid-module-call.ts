// A module function's result is its annotation: it cannot establish null.
function flag(x: boolean): boolean {
  return x;
}
export function wrong(x: boolean): null {
  return flag(x);
}
