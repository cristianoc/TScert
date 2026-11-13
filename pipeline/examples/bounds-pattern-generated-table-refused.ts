// Bounds pattern P5: bounds held by the contents of generated tables.
// Fact: forall i in t: 0 <= t[i] < t.length for the decoded table, so an
// entry read from it indexes it again.
// Pretext: line-breaks.ts unpackTable, getClass, unpackClassRuns,
// unpackStateRows, markRuleBoundaries; gecko-line-breaks.ts markWordBreaks;
// measurement.ts getWebKitGenericFamilies; prepare.ts getScriptFacts (16 sites).
// Gap: the fact holds because the data is what its generator wrote; the
// decoder copies the bytes without testing them, and no step establishes it.
// (The document's program caches the table in a module cell, whose first
// blocker is P16 at `t[state]`; here the table is decoded at each call.)
/** @ensures result.length === 4 */
function decode(): Uint8Array {
  const packed = "\u0003\u0001\u0002\u0000";
  const out = new Uint8Array(4);
  for (let i = 0; i < 4; i++) out[i] = packed.charCodeAt(i) & 0xff;
  return out;
}

/** @requires safeInteger(state) && 0 <= state && state < 4 */
export function next(state: number): number {
  const t = decode();
  return t[t[state]!]!;
}
