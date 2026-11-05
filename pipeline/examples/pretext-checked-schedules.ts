// pretext: getExtraSpacings, measureFitAdvances, getUnspacedGraphemes.
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
