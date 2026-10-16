// `instanceof` of a value typed `Function`: TypeScript's type states the
// `[Symbol.hasInstance]` the standard library declares on `Function`, which
// `Function.prototype` holds and no program declared. It is no typed hook: the
// right operand is a constructor from elsewhere, whose prototype test is
// refused.
class Hooked {
  static [Symbol.hasInstance](x: object): boolean {
    return x !== null;
  }
}
export function test(x: object, k: Function): boolean {
  return x instanceof k;
}
export function hooked(x: object): boolean {
  return x instanceof Hooked;
}
