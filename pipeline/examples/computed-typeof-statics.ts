// `typeof C` of a class with static fields is the class value's type: its
// construct signature and its static fields, own data properties of the
// class value, each at its annotation or, without one, at the literal type
// TypeScript gives its readonly literal initializer.
class C {
  static readonly zero: number = 0;
  static readonly unit = 1;
  value: number = 2;
}
export function make(K: typeof C): C {
  return new K();
}
export function read(K: typeof C): number {
  return K.zero + K.unit;
}
export function pass(): number {
  return read(C) + make(C).value;
}
