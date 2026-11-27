// Negative control: an omitted Object.prototype key (`toString`) is inherited
// on every plain object literal in JavaScript (reading a function, never
// `undefined`), so `ValueSet.omitsKey` must exclude `Calculus.inheritedKey`
// and refuse an invariant relying on `this.toString === undefined`.

/** @invariant this.toString === undefined || this.widths.length >= 1 */
type WithToString = {
  widths: number[];
  toString?: () => string;
};

export function makePlainWithEmptyWidths(): WithToString {
  return { widths: [] };
}
