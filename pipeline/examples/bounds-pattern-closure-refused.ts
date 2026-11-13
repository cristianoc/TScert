// Bounds pattern P7: a fact over a local closure's captures.
// Fact: at the closure's entry, glyphs.length = 4, 0 <= from and to <= 4,
// with `glyphs` a captured `const`.
// Pretext: han-kerning.ts getHanKerningTrims (addWidthTrim), getFontData
// (group); rich-inline.ts prepareRichInline (10 sites).
// Gap: a closure's clauses name only its parameters, so the edge into its
// loop lacks to <= glyphs.length.
type Glyph = { advance: number };

export function groups(): number {
  const glyphs: Glyph[] = [{ advance: 1 }, { advance: 2 }, { advance: 3 }, { advance: 4 }];
  const group = (from: number, to: number): number => {
    let s = 0;
    /** @invariant safeInteger(i) && safeInteger(to) && 0 <= i && to <= glyphs.length */
    for (let i = from; i < to; i++) s += glyphs[i]!.advance;
    return s;
  };
  return group(0, 2) + group(2, 4);
}
