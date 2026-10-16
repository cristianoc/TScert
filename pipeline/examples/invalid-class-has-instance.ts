// `x instanceof Anything` calls the class's static `[Symbol.hasInstance]`,
// which answers true of every value: the test does not make `x` an
// `Anything`, where TypeScript narrows it to one.
class Anything {
  a: number = 1;
  static [Symbol.hasInstance](_x: unknown): boolean {
    return true;
  }
}

export function narrowed(x: Anything | number): Anything {
  if (x instanceof Anything) return x;
  return new Anything();
}
