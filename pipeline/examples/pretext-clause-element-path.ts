// Pretext findSegmentSources/materializeRichInlineLineRange: a quantified
// element's length and data paths bound later indexed reads.
/**
 * @requires safeInteger(index) && 0 <= index && index < xs.length
 * @requires forall i in xs: xs[i].length < bounds.length
 */
export function byLength(
  xs: string[],
  bounds: number[],
  index: number,
): number {
  const text = xs[index]!;
  return bounds[text.length]!;
}

/**
 * @requires safeInteger(index) && 0 <= index && index < xs.length
 * @requires forall i in xs: xs[i].text.length < bounds.length
 */
export function byPath(
  xs: { text: string }[],
  bounds: number[],
  index: number,
): number {
  const item = xs[index]!;
  return bounds[item.text.length]!;
}

/**
 * @requires safeInteger(index) && 0 <= index && index < xs.length
 * @requires forall i in xs: safeInteger(xs[i].offset) && 0 <= xs[i].offset && xs[i].offset < bounds.length
 */
export function byIntegerPath(
  xs: { offset: number }[],
  bounds: number[],
  index: number,
): number {
  const item = xs[index]!;
  return bounds[item.offset]!;
}

/**
 * @requires safeInteger(index) && 0 <= index && index < xs.length
 * @requires forall i in xs: xs[i].length < bounds.length
 */
export function byDirectLength(
  xs: string[],
  bounds: number[],
  index: number,
): number {
  return bounds[xs[index]!.length]!;
}
