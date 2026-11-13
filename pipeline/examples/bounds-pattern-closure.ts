// Bounds pattern P7, the supported neighbour of `bounds-pattern-closure-refused`:
// the same reads in the function's own body.
// Pretext: han-kerning.ts getFontData.
type Glyph = { advance: number };

export function inline(): number {
  const glyphs: Glyph[] = [{ advance: 1 }, { advance: 2 }, { advance: 3 }, { advance: 4 }];
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && glyphs.length === 4 */
  for (let i = 0; i < 4; i++) s += glyphs[i]!.advance;
  return s;
}
