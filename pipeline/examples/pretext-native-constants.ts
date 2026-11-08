// Pretext's measurement.ts and line-breaks.ts: constants annotated
// `RegExp` and `ReadonlyMap` whose initializers make a regex literal and a
// `Map`, read at the native objects they hold, and a locale tag cut down by
// `lastIndexOf` and `slice` while a lookup misses. Each call is within a
// footprint keeping stores, so a loop's `tags[i]!` keeps its bound across
// them.
const kanaPairRe: RegExp = /[ぁ-ヿ]{2}/
const families: { [tag: string]: readonly number[] } = { 'zh': [1, 2], 'ja': [3] }
const familyTable: ReadonlyMap<string, readonly number[]> = new Map(Object.entries(families))

function familiesOf(tag: string): number {
  let row = familyTable.get(tag)
  while (row === undefined) {
    tag = tag.slice(0, Math.max(0, tag.lastIndexOf('-')))
    if (tag === '') return 0
    row = familyTable.get(tag)
  }
  return row.length
}

export function count(tags: string[]): number {
  let sum = 0
  for (let i = 0; i < tags.length; i++) {
    sum += familiesOf(tags[i]!) + (kanaPairRe.test(tags[i]!) ? 1 : 0)
    sum += tags[i]!.length
  }
  return sum
}
