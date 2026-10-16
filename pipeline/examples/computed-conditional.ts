// `Extract<T, U>` and `Exclude<T, U>` distribute over the members of `T`'s
// union: each is the union of the members TypeScript keeps, each member
// read as declared. A user alias distributing over its parameter is read
// the same way, and one TypeScript computes to literals is those literals.
type Shape = { k: "a"; x: number } | { k: "b"; y: string } | Circle;
interface Circle {
  k: "c";
  r: number;
}
type Tag = "p" | "q" | { tag: string };
type Strings<T> = T extends string ? T : never;
type KeysOf<T> = T extends unknown ? keyof T : never;
function readA(s: Extract<Shape, { k: "a" }>): number {
  return s.x;
}
function readRound(s: Extract<Shape, { r: number }>): number {
  return s.r;
}
function notA(s: Exclude<Shape, { k: "a" }>): string {
  return s.k === "b" ? s.y : "c";
}
function tags(t: Extract<Tag, string>): "p" | "q" {
  return t;
}
function own(t: Strings<Tag>): string {
  return t;
}
function key(k: KeysOf<Shape>): string {
  return k;
}
export function use(): number {
  return (
    readA({ k: "a", x: 1 }) +
    readRound({ k: "c", r: 2 }) +
    notA({ k: "b", y: "s" }).length +
    tags("p").length +
    own("q").length +
    key("x").length
  );
}
