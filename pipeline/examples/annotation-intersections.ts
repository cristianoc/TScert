// An annotation's intersection is the meet of its operands: named records
// and interfaces are one object, and primitives reduce as TypeScript reduces
// them (`string & "fixed"` is `"fixed"`, `number & string` is `never`).
interface A {
  a: number;
}
interface B {
  b: string;
}
type C = { c: boolean };
function both(x: A & B & C): number {
  return x.a + x.b.length + (x.c ? 1 : 0);
}
function fixed(s: string & "fixed"): "fixed" {
  return s;
}
function impossible(f: (x: number) => number & string): (x: number) => never {
  return f;
}
export function use(): number {
  return both({ a: 1, b: "", c: true }) + fixed("fixed").length;
}
