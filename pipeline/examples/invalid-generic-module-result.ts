// An instance's result is the instantiated type, not another.
function same<T>(x: T): T {
  return x;
}
export function wrong(flag: boolean): null {
  return same(flag);
}
