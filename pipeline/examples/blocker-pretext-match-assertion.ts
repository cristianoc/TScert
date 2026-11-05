// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#countEmojiGlyphs.
// Refusal: reject: source expression obligation: no derivation of its cast
// claim.
// A non-null assertion of a `match` with a global regular expression, after
// another expression's `test` passed: the match is found because every code
// point the tested expression matches is one the matched one's class
// admits, an inclusion of Unicode properties that no type states.
const presentationRe = /\p{Emoji_Presentation}|\p{Extended_Pictographic}/u;
const stretchRe = /[\p{Extended_Pictographic}\p{Emoji_Component}]+/gu;

export function stretches(grapheme: string): number {
  if (!presentationRe.test(grapheme)) return 0;
  return grapheme.match(stretchRe)!.length;
}
