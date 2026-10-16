// A static `[Symbol.hasInstance]` makes `instanceof` a call of that method
// with the operand, its result converted to a Boolean: no prototype is
// walked, and the test narrows nothing. A derived class inherits its base's.
class Anything {
  a: number = 1;
  static [Symbol.hasInstance](_x: unknown): boolean {
    return true;
  }
}
class Derived extends Anything {
  b: number = 2;
}
class HasValue {
  static [Symbol.hasInstance](x: { value: number }): boolean {
    return x.value > 0;
  }
}

export function keeps(x: Anything): number {
  if (x instanceof Anything) return x.a;
  return x.a;
}

export function inherited(x: unknown): boolean {
  return x instanceof Derived;
}

export function argument(x: { value: number }): boolean {
  const matched = x instanceof HasValue;
  return !matched;
}
