/**
 * Exercise the source gate for a mutable local with neither an initializer
 * nor an annotation. An initialized `let` is in the fragment, with a storage
 * contract either written or supplied by the producer and checked, and so is
 * an annotated `let y: T;`, a cell of contract `T | undefined` holding
 * `undefined`. This one has no contract at all: TypeScript gives it an
 * evolving `any`, which is no type every write could be checked against.
 */
function pick(flag: boolean): boolean {
  let y;
  y = flag;
  return y;
}
