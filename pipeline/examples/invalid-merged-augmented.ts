// A class merged with an interface adding a member: TypeScript assumes `m`
// on instances the class's construction does not give it, which reads
// `undefined` as a number.
class C {}
interface C {
  m: number;
}
export function f(x: C): number {
  return x.m;
}
