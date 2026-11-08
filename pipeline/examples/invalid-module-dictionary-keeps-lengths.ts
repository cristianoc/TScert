// A module dictionary filled at a key, beside a pop of a module array the
// caller reads: the lookup changes a store, so past its call the caller's
// bound is lost. Under Node the second call empties `seen`, and `seen[0]!`
// reads `undefined`.
type Table = 'a' | 'b'
const cache: Partial<Record<Table, number>> = {}
const seen: number[] = [1, 2]

function get(t: Table): number {
  seen.pop()
  return cache[t] ?? (cache[t] = t.length)
}

export function first(t: Table): number {
  if (seen.length === 0) return 0
  get(t)
  return seen[0]!
}
