// A class's generic method with a bounded binder: the member's binder row is
// named by its bound, which the closure's binder is not yet named by.
class Helper {
  pick<V extends number>(a: V): V {
    return a;
  }
}
export function use(h: Helper): number {
  return h.pick(1);
}
