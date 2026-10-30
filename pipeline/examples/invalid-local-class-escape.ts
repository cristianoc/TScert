// A class declared in a block handed to a callback, which may define its
// `[Symbol.hasInstance]` (run under Node: `0 instanceof Held` is then true,
// and the field read gives undefined): refused at the read passing it.
export function held(define: (cls: unknown) => void, zero: boolean): number {
  class Held {
    readonly n: number = 1;
  }
  define(Held);
  const value: Held | number = zero ? 0 : new Held();
  return value instanceof Held ? value.n : value;
}
