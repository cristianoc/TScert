// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// gecko-line-breaks.ts#transformText.
// Refusal: reject: source expression obligation: no derivation of its cast
// claim.
// A non-null assertion of a nullable local whose non-null state is implied
// by another local's value (`starts === null` makes `end` the length, so `i
// >= end` never holds then): the correlation between the two is not known.
export function frames(len: number, starts: number[] | null): number {
  let frame = 0;
  const end = starts === null ? len : 0;
  for (let i = 0; i < len; i++) {
    if (i >= end) while (frame < starts!.length) frame++;
  }
  return frame;
}
