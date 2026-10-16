// A spread copies its operand's own enumerable properties, when it is
// evaluated, onto the object built so far: each spread is a merge onto a
// fresh accumulator (DESIGN.md, "Object literals"). A field after a spread
// is surely the literal's; a field the operand's type names is surely the
// operand's; a copy's fields are writable, whatever the operand's were.
function copy(o: { a: number }): { a: number } {
  return { ...o };
}
function after(o: { a: number }): { a: number; b: string } {
  return { ...o, b: "hello" };
}
function overwritten(o: { a: number }): { a: number } {
  return { a: 0, ...o };
}
function writable(o: { readonly a: number }): number {
  const c = { ...o };
  c.a = 2;
  return c.a;
}
// An optional field the operand may hold: the result holds one or the other.
function optionalOverlap(o: { a?: number }): { a: string | number } {
  return { a: "", ...o };
}
// A spread of `false` copies nothing; a fresh literal owns exactly its keys.
function conditional(cond: boolean): { x: number; y?: number } {
  return { x: 0, ...(cond && { y: 1 }) };
}
// A union distributes: each alternative is spread on its own.
function union(
  x: { a: number } | { b: string },
): { a: number; k: boolean } | { b: string; k: boolean } {
  return { ...x, k: true };
}
// A class instance's fields are its own; its methods are its prototype's.
class Counter {
  count: number = 1;
  next(): number {
    return this.count + 1;
  }
}
function instance(c: Counter): { count: number } {
  return { ...c };
}
export function main(): number {
  return (
    copy({ a: 1 }).a +
    after({ a: 1 }).a +
    overwritten({ a: 1 }).a +
    writable({ a: 1 }) +
    instance(new Counter()).count
  );
}
