// A function wider than the element that declares a `this` parameter: `map`
// calls its callback with `undefined` as the receiver, which it returns.
type F = { k: "f"; n: number };
type A = { k: "a"; s: string };
type T = A | F;
type Named = { s: string };

export function wrong(calls: F[]): Named[] {
  const self = function (this: Named, _t: T): Named {
    return this;
  };
  return calls.map(self);
}
