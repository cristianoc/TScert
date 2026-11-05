// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// prepare.ts#addIdeographicSpaceHangs, prepare.ts#addKanaKerning,
// prepare.ts#getJoinedNarrowing, prepare.ts#getTailKerning,
// prepare.ts#getTextSegmentWidth, prepare.ts#measureAnalysis.
// Refusal: gate: a declared value must be an annotated constant, function
// or class: kanaPairRe.
// An imported constant holding a regular expression literal, with no
// annotation: it states no type, so its use is refused. TypeScript's
// `isolatedDeclarations` refuses the declaration too (TS9010, TypeScript
// 5.9, 6.0 and 7.0): a regular expression literal is not one it declares a
// type from. The source states `: RegExp`.
import { kanaPairRe } from "../pretext-project/measurement.ts";

export function hasKanaPair(segment: string): boolean {
  return kanaPairRe.test(segment);
}
