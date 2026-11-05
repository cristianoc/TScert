// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): prepare.ts#measureAnalysis.
// Refusal: reject: closure expression claim: evidence search failed.
// A flags byte masked to its kind bits and asserted to the union of the
// kind codes, `(flags & 0x0f) as Kind`: the mask leaves 0 to 15, and that
// every stored byte's low bits hold a kind is an invariant of the array's
// writers, which no type states. The code reads the masked number as it
// is; only `=== ZERO_WIDTH_BREAK` reads it further.
type Kind = 0 | 1 | 2;

function spaced(kind: Kind): number {
  return kind === 2 ? 0 : 1;
}

export function count(flags: Uint8Array, i: number): number {
  const kind = ((flags[i] ?? 0) & 0x0f) as Kind;
  return spaced(kind);
}
