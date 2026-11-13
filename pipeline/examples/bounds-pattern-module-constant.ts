// Bounds pattern P15, the supported neighbour of
// `bounds-pattern-module-constant-refused`: the same literal declared in the function.
// Pretext: layout.ts prepareWithSegments.
/** @requires safeInteger(f) && 0 <= f && f < 256 */
export function kindNameLocal(f: number): string {
  const kinds = ["a", "b", "c", "d"];
  return kinds[f & 3]!;
}
