// Pretext rich-inline.ts builders retain itemSegments facts across
// operations whose checked footprint keeps the cells those facts read.
/** @requires safeInteger(k) && 0 <= k && k < ends.length
 * @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
export function afterStringWrite(widths: number[], ends: number[], k: number, box: {label: string}): number {
  box.label = "written";
  return widths[ends[k]!]!;
}
