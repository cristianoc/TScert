// A class merged with an interface adding a member: constructing it must
// give the whole contract, and its construction does not create `m`, which
// JavaScript reads `undefined` though TypeScript types it a number.
class C {}
interface C {
  m: number;
}
export function f(): number {
  return new C().m;
}
