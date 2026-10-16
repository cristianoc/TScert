// A mapped type's keys are the union TypeScript computes for them: an alias
// of literals, or `keyof` a record, gives one field per key, as the literals
// written would; over `string | number`, a string index, since every
// numeric key is a string key.
type Key = "a" | "b";
type Point = { x: number; y: number };
type Both = Record<string | number, number>;
function flags(): Record<Key, number> {
  return { a: 1, b: 2 };
}
function mapped(): { [P in Key]: string } {
  return { a: "x", b: "y" };
}
function copy(p: Point): Record<keyof Point, number> {
  return { x: p.x, y: p.y };
}
function read(x: Both): number | undefined {
  return x["k"];
}
export function use(): number {
  return flags().a + mapped().b.length + copy({ x: 1, y: 2 }).y;
}
