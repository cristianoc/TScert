// A meet of two records is not the meet of three.
interface A {
  a: number;
}
interface B {
  b: string;
}
type C = { c: boolean };
export function bad(x: A & B): A & B & C {
  return x;
}
