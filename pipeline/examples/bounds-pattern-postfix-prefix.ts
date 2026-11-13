// Bounds pattern P13, the supported neighbour of
// `bounds-pattern-postfix-prefix-refused`: the prefix filled with a postfix
// counter in the function's own body, over a fresh view.
// Pretext: graphemes.ts findGraphemeEnds.
/** @requires text.length <= 2147483647 */
export function local(text: string): number {
  const ends = new Int32Array(text.length);
  let count = 0;
  /** @invariant safeInteger(count) && 0 <= count && count <= ends.length && ends.length === text.length && forall k < count of ends: safeInteger(ends[k]) && 0 < ends[k] && ends[k] <= text.length */
  while (count < ends.length) {
    const v = count + 1;
    ends[count++] = v;
  }
  return count > 0 ? text.codePointAt(ends[0]! - 1)! : 0;
}
