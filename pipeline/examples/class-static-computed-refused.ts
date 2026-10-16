// A static member with a computed key other than `[Symbol.hasInstance]`,
// which `instanceof` calls, is refused: a static member is a binding named
// by its plain name, and nothing reads a static symbol-keyed member.
class Anything {
  static [Symbol.toPrimitive](_hint: string): number {
    return 0;
  }
}
export function make(): Anything {
  return new Anything();
}
