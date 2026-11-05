// pretext: getExtraSpacings, measureFitAdvances, countEmojiGlyphs, getUnspacedGraphemes,
// findSegmentSources and isEastAsianSegmentBreak.
function defined<T>(value: T | undefined): T {
  if (value === undefined) throw new RangeError('missing endpoint')
  return value
}
export function pieces(text: string, ends: number[]): string[] {
  const pieces: string[] = []
  for (let i = 0; i < ends.length; i++) {
    const start = i === 0 ? 0 : defined(ends[i - 1])
    const end = defined(ends[i])
    if (end === start) continue
    pieces.push(text.slice(start, end))
  }
  return pieces
}
export function selected(inside: number[] | null, fill: number[] | null, g: number, i: number): number {
  const extra = g > 1 ? inside : fill
  return extra === null ? 0 : defined(extra[i])
}

export function offsets(segments: string[]): number[] {
  const offsets: number[] = []
  let at = 0
  for (let i = 0; i < segments.length; i++) {
    offsets.push(at)
    at += defined(segments[i]).length
  }
  return offsets
}
export function skipIgnorable(text: string, start: number): number {
  let before = 0
  let pos = start
  do {
    before = text.charCodeAt(pos - 1)
    pos--
  } while (before === 0x200b && pos > 0)
  return before
}
