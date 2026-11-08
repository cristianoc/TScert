// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// prepare.ts#addIdeographicSpaceHangs, prepare.ts#addKanaKerning,
// prepare.ts#getJoinedNarrowing, prepare.ts#getTailKerning,
// prepare.ts#getTextSegmentWidth, prepare.ts#measureAnalysis.
// An imported constant holding a regular expression literal, with no
// annotation: the importer reads it at the literal's native type, as its
// module reads it.
import { kanaPairRe } from "../pretext-project/measurement.ts";

export function hasKanaPair(segment: string): boolean {
  return kanaPairRe.test(segment);
}
