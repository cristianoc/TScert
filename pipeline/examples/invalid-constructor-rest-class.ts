class Two {
  a: number;
  b: number;
  constructor(a: number, b: number) {
    this.a = a;
    this.b = b;
  }
}
function make(ctor: new (...params: number[]) => Two): string {
  return new ctor(1).b.toFixed();
}
// TypeScript accepts a class of two required parameters where a variadic
// construct signature is expected; `new ctor(1)` binds `b` to `undefined`,
// and `toFixed` throws.
export const made = make(Two);
