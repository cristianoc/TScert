// An early `let` initialized by a `const enum` member: TypeScript's declared
// type for it is the enum, not the member's number, so the initializer is no
// literal of the source and the binding's type is not stated: refused.
const enum E {
  A = 0,
}
export function member(): number {
  const read = (): number => x;
  let x = E.A;
  return read();
}
