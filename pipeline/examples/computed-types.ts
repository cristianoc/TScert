// Types TypeScript computes from other types are the types they evaluate to:
// `typeof` of a constant, a function, a class, a member and `undefined`;
// `keyof` of a record and an interface; an indexed access into a record, a
// tuple and an array; a template literal type over literal holes, and one
// without holes. `typeof` of a narrowed binding is its narrowed type.
interface Person {
  name: string;
  age: number;
}
type Keys = keyof Person;
type Pair = [string, { readonly n: number }];
type Row = { cells: number[]; meta: { tag: string } };
type Greeting = `hello ${"world" | "there"}`;
const limit: number = 10;
const box: { readonly value: { readonly n: number } } = { value: { n: 1 } };
class Point {
  x: number;
  constructor(x: number) {
    this.x = x;
  }
}
function twice(n: number): number {
  return n * 2;
}
function pick(k: Keys): string {
  return k === "name" ? "name" : "age";
}
function second(p: Pair): Pair[1] {
  return p[1];
}
function meta(r: Row): Row["meta"] {
  return r.meta;
}
function cell(r: Row): Row["cells"][number] | undefined {
  return r.cells[0];
}
function inner(): typeof box.value {
  return box.value;
}
function build(Ctor: typeof Point, f: typeof twice, n: typeof limit): Point {
  return new Ctor(f(n));
}
function nothing(): typeof undefined {
  return undefined;
}
function greet(g: Greeting): string {
  return g;
}
// `typeof x` where `x` is narrowed is the narrowed type, as TypeScript reads it.
function narrowed(x: string | number): string {
  if (typeof x === "string") {
    const y: typeof x = x;
    return y;
  }
  return "";
}
enum Color {
  Red,
  Green,
}
// `keyof typeof E` is the enum's member names.
function colorName(k: keyof typeof Color): string {
  return k;
}
function plain(): `abc` {
  return "abc";
}
export function use(): number {
  const k: keyof { a: number; b: string } = "b";
  const g: Greeting = "hello there";
  return (
    pick("age").length +
    meta({ cells: [1], meta: { tag: k } }).tag.length +
    (cell({ cells: [3], meta: { tag: "" } }) ?? 0) +
    inner().n +
    build(Point, twice, limit).x +
    (nothing() === undefined ? 1 : 0) +
    greet(g).length +
    plain().length +
    colorName("Green").length
  );
}
