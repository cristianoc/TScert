// An object type with a construct signature and properties is a class value
// holding them as its static fields, own data properties under invariant
// contracts: a class with those static fields at those types meets it.
class C {
  static readonly zero: number = 0;
  static readonly label: string = "c";
  value: number = 1;
}
type Maker = { new (): C; zero: number; label: string };
export function make(K: Maker): number {
  return new K().value + K.zero + K.label.length;
}
export function pass(): number {
  return make(C);
}
