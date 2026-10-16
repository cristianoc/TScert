// An object type with a construct signature and a readonly property states
// a class value whose static field it may only read, a view: a class whose
// static field holds a narrower type meets it.
class C {
  static readonly zero: 0 = 0;
  value: number = 1;
}
export function make(K: { new (): C; readonly zero: number }): number {
  return new K().value + K.zero;
}
export function pass(): number {
  return make(C);
}
