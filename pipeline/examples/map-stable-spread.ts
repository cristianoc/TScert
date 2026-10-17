// `map` callbacks building arrays with spreads: of an array, which reads its
// store; of a regex's matches, a set and a string, each through the host's
// iterator, which writes only its own position and allocates what it yields.
// Each callback is within `{value: any, store: keep}`, so the results are
// dense.
export function padded(rows: number[][]): number[][] {
  return rows.map((r: number[]): number[] => [0, ...r, 0]);
}
export function matchCounts(lines: string[]): number[] {
  return lines.map((l: string): number => [...l.matchAll(/a/g)].length);
}
export function distinctCounts(rows: string[][]): number[] {
  return rows.map((r: string[]): number => [...new Set(r)].length);
}
export function codePoints(words: string[]): number[] {
  return words.map((w: string): number => [...w].length);
}
