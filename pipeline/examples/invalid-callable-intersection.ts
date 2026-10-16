// `{ (): string } & { (): number }` is a callable meeting both signatures,
// which a function that never returns does (`() => { throw 0; }`), not an
// empty type: returning the union as a string may return that function.
declare function getCallableInter(): ({ (): string } & { (): number }) | string;
export function testCallableInter(): string {
  return getCallableInter();
}
