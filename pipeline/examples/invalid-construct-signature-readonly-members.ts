// A readonly static field of a construct type is read at its type: a class
// whose static field holds a string does not meet a number view.
class C {
  static readonly zero: string = "0";
  value: number = 1;
}
export function make(K: { new (): C; readonly zero: number }): number {
  return new K().value + K.zero;
}
export function pass(): number {
  // @ts-expect-error a string field is not a number view
  return make(C);
}
