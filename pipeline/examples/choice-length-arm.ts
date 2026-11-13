// A choice whose arm reads a length (`trailing = cut ? tail(s, 0) :
// s.length`) and a choice of that binding and `0`: the loop head after them
// is proposed what both arms establish, each arm's fact kept where the other
// arm, with the facts before the choice, entails it (`Ctx.join`): `0 <=
// trailing <= s.length`, then `0 <= from` (pretext's `analyzeText`, its
// Gecko branch's copy loop).
/** @requires safeInteger(from) && 0 <= from
 * @ensures safeInteger(result) && 0 <= result && result <= text.length */
function tail(text: string, from: number): number {
  let start = text.length;
  /** @invariant safeInteger(start) && 0 <= start && start <= text.length */
  for (let i = text.length - 1; i >= from; i--) {
    if (text.charCodeAt(i) === 32) start = i;
    else break;
  }
  return start;
}

/** @ensures result.length === source.length + 1 */
function scan(source: string): Uint8Array {
  return new Uint8Array(source.length + 1);
}

export function sumFrom(source: string, cut: boolean, left: Uint8Array | null): number {
  const b = scan(source);
  const trailing = cut ? tail(source, 0) : source.length;
  const from = left === null ? trailing : 0;
  let sum = 0;
  for (let i = from; i < source.length; i++) sum += b[i]!;
  return sum;
}
