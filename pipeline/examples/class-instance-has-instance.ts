// `Symbol.hasInstance` is a host hook only where `instanceof` reads it, off
// its right operand. An instance method keyed by it is an
// ordinary prototype key: called as any method, and `instanceof` of its
// class still walks the operand's prototype chain.
class Matcher {
  a: number = 1;
  [Symbol.hasInstance](x: { value: number }): boolean {
    return x.value > this.a;
  }
}

export function call(m: Matcher, x: { value: number }): boolean {
  return m[Symbol.hasInstance](x);
}

export function test(x: Matcher): number {
  if (x instanceof Matcher) return x.a;
  return x.a;
}

export function literal(): { [Symbol.hasInstance](x: number): boolean } {
  return {
    [Symbol.hasInstance](x: number): boolean {
      return x > 0;
    },
  };
}
