// A source alias spelling a generated name with an escape: the evaluator
// takes another name. Only the escaped spellings occur, so the generated
// names collide and are replaced. (Prettier would decode the escapes.)
type __TScertProbe0<T, K> = number;
type __TScertUse0 = number;
type G<T, K extends keyof T> = K;
export function f(x: keyof { z: G<{ a: number }, "a"> }): "z" {
  return x;
}
