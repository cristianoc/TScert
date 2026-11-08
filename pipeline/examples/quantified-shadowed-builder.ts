// Pretext rich-inline.ts's prepareRichInline: a block's builder declares
// the same name as the function's later builder, and its loop invariant
// names the block's own array.
/** @requires safeInteger(n) && 0 <= n */
export function build(widths: number[], n: number): number {
  if (n === 0) {
    const ends: number[] = []
    /** @invariant forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] <= widths.length */
    for (let i = 0; i <= n; i++) ends.push(widths.length)
    return ends.length
  }
  const ends: number[] = []
  ends.push(0)
  return ends.length
}
