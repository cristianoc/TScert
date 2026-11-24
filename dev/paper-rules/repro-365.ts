// Issue #365.
// A cursor inside a segment indexes that segment's per-grapheme list: its
// grapheme index is below the length of the list at its segment index. An
// indexed-element clause bounds `c.graphemeIndex` by the length of the array
// read at `h.advances[c.segmentIndex]`.

type Cursor = { segmentIndex: number; graphemeIndex: number };
type Handle = { advances: (number[] | null)[] };

// Verified by the ordinary verifier using the indexed-element length clause.
/** @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length
 *  @requires safeInteger(c.graphemeIndex) && 0 <= c.graphemeIndex
 *  @requires h.advances[c.segmentIndex] === null || c.graphemeIndex < h.advances[c.segmentIndex].length */
export function startAdvance(h: Handle, c: Cursor): number {
  const advances = h.advances[c.segmentIndex];
  if (advances === undefined || advances === null) return 0;
  return advances[c.graphemeIndex]!;
}

// `paperAssume(fact, "#N");` is the prototype's unsafe assume: the prototype
// checks it as `if (!(fact)) throw "#N";`, so past it the pass knows `fact`
// as on the branch where it holds, and names the issue in its verdict; the
// ordinary verifier reads it as a call that changes nothing.
function paperAssume(fact: boolean, issue: string): Modifies<{}, void> {}

// Accepted by the prototype, naming #365; refused by the ordinary verifier.
/** @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length */
export function startAdvanceAssumed(h: Handle, c: Cursor): number {
  const advances = h.advances[c.segmentIndex];
  if (advances === undefined || advances === null) return 0;
  const g = c.graphemeIndex;
  paperAssume(Number.isSafeInteger(g) && 0 <= g, "#365"); // unsafe assume until #365
  paperAssume(g < advances.length, "#365"); // unsafe assume until #365
  return advances[g]!;
}

// Refused (unprovable): the assumed facts give no lower bound.
/** @requires safeInteger(c.segmentIndex) && 0 <= c.segmentIndex && c.segmentIndex < h.advances.length */
export function startAdvanceWeak(h: Handle, c: Cursor): number {
  const advances = h.advances[c.segmentIndex];
  if (advances === undefined || advances === null) return 0;
  const g = c.graphemeIndex;
  paperAssume(g < advances.length, "#365"); // unsafe assume until #365
  return advances[g]!;
}
