// Bounds pattern P15: a module constant array.
// Fact: KINDS.length = 4 at each entry of `kindName`.
// Pretext: layout.ts prepareWithSegments; line-breaks.ts hasProperty;
// prepare.ts needsComplexTextPath (4 sites).
// Gap: the module binding holds one array, whose store no contract fixes,
// so its length at allocation is not known at a function's entry.
const KINDS: readonly string[] = ["a", "b", "c", "d"];

/** @requires safeInteger(f) && 0 <= f && f < 256 */
export function kindName(f: number): string {
  return KINDS[f & 3]!;
}
