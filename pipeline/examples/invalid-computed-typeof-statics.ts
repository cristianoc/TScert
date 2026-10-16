// A class whose static field holds a string is not a `typeof C` whose static
// field holds a number: the static field is one of the class value's type.
class C {
  static readonly zero: number = 0;
}
class D {
  static readonly zero: string = "0";
}
export function read(K: typeof C): number {
  return K.zero;
}
export function pass(): number {
  // @ts-expect-error a string field is not a number field
  return read(D);
}
