// A method is not a function-valued property: the property promises a call on
// any receiver, the method only on its own object.
class Counter {
  count: number = 0;
  get(): number {
    return this.count;
  }
}
export function asProperty(c: Counter): { readonly get: () => number } {
  return c;
}
