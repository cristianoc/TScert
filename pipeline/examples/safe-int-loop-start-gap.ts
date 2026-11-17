// A loop starting at a value merged from a call returning `SafeInt` and a
// `number` (pretext's `analyzeText` reading `getTrailingCollapsibleStart`
// typed `SafeInt`): the loop head's facts over the counter, `0 <= i`, are
// not established, so the bounded read `marks[i]` is refused. With the
// callee's result typed `number` and `@ensures safeInteger(result)` the same
// loop verifies.

/** @ensures 0 <= result && result <= s.length */
function trailing(s: string): SafeInt {
  if (s.length > 5) return 5;
  return 0;
}

export function sumFrom(s: string, b: boolean, c: boolean): number {
  const marks = new Uint8Array(s.length + 1);
  const t = b ? trailing(s) : s.length;
  const from = c ? t : 0;
  let r = 0;
  for (let i = from; i < s.length; i++) r += marks[i]!;
  return r;
}
