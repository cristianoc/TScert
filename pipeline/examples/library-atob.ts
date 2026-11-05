// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-breaks.ts#unpackTable, line-breaks.ts#unpackVarints.
// The DOM's `atob` of a string, which no conversion code runs on: a fresh
// string of the decoded bytes, or a thrown DOMException, an outcome; it
// writes nothing.
export function bytes(data: string): number {
  return atob(data).length;
}
