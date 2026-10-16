// A field without an initializer holds `undefined` from the instance's
// creation: `alias?: string` is then present at `undefined`, which the exact
// optional field `alias?: string` of a record type does not admit. (TypeScript
// accepts this.)
class Maybe {
  alias?: string;
}
export function make(): { alias?: string } {
  return new Maybe();
}
