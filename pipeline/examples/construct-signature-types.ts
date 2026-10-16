// An interface of construct signatures only is a class value meeting each,
// read as such a type literal is (`construct-signature-literal.ts`).
class C {
  x: number = 1;
}
interface Maker {
  new (): C;
}
function make(K: Maker): C {
  return new K();
}
export function use(): number {
  return make(C).x;
}
