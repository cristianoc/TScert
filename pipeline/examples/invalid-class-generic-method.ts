// A class's generic method is checked at every instance of its binder: a
// body returning its number where the binder is promised is refused.
class Helper {
  pick<V>(a: V, b: number): V {
    // @ts-expect-error a number is not a V
    return b;
  }
}
export function make(): Helper {
  return new Helper();
}
