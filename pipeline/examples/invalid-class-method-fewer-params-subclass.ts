// A subclass overriding `m(a: number)` with an optional second parameter
// `m(a: number, b?: string)` cannot meet `Base.m`'s `(a: number, ...unknown[])`
// contract: TypeScript accepts `bad()`, which throws `TypeError` under Node
// when `42` reaches `b.toUpperCase()`.
class Base {
  m(a: number): string {
    return "" + a;
  }
}

class Sub extends Base {
  m(a: number, b?: string): string {
    return b !== undefined ? b.toUpperCase() : "" + a;
  }
}

interface TwoNum {
  m(a: number, b: number): string;
}

export function bad(): string {
  const b: Base = new Sub();
  const t: TwoNum = b;
  return t.m(1, 42);
}
