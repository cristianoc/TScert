// Bounds pattern P15, the unsafe neighbour of
// `bounds-pattern-module-constant-refused`: a module array that another
// function pops (run under Node after `drop()`: `undefined` at `string`). An
// immutable-content contract must exclude every write of the store.
const KINDS: string[] = ["a", "b", "c", "d"];

export function drop(): void {
  KINDS.pop();
}

/** @requires safeInteger(f) && 0 <= f && f < 256 */
export function kindName(f: number): string {
  return KINDS[f & 3]!;
}
