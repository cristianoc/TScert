// Pretext's graphemes.ts and line-breaks.ts: a module dictionary of rules,
// filled at a table's first use (`graphemeRules[table] ??= …`,
// `breakRules[table] = …`). The write at a string key copies the dictionary
// with the key and rebinds the module's binding, a cell holding a value, so
// each lookup is within {value: any, store: keep} and a caller's loop keeps
// its bound across it.
type Table = 'a' | 'b'
type Rules = { n: number }
const cache: Partial<Record<Table, Rules>> = {}

function parse(t: Table): Rules {
  return { n: t.length }
}

function get(t: Table): Rules {
  return cache[t] ?? (cache[t] = parse(t))
}

export function total(ts: Table[]): number {
  let sum = 0
  for (let i = 0; i < ts.length; i++) sum += get(ts[i]!).n + ts[i]!.length
  return sum
}
