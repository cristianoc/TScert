// An object type with a construct signature and an optional property states
// a class value that may lack a static field: a class value's static fields
// are required data properties here.
class C {
  static readonly zero: number = 0;
}
export function make(K: { new (): C; zero?: number }): C {
  return new K();
}
