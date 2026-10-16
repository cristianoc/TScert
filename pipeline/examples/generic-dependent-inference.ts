// TypeScript's implicit inference chooses U = true and rejects this call.
// U = boolean, T = boolean is valid; the independent verifier checks that proposal.
function propagatedBound(flag: boolean): boolean {
  const pick = <U, T extends U>(first: U, second: T): U => second;
  return pick(true, flag);
}
