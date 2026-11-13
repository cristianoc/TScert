// Bounds pattern P7, the unsafe neighbour of `bounds-pattern-closure-refused`:
// the closure called past the captured array's end (run under Node: a
// TypeError at `undefined.advance`). A clause over captures must be
// established at each call.
type Glyph = { advance: number };

export function pastEnd(): number {
  const glyphs: Glyph[] = [{ advance: 1 }, { advance: 2 }, { advance: 3 }, { advance: 4 }];
  const group = (from: number, to: number): number => {
    let s = 0;
    /** @invariant safeInteger(i) && safeInteger(to) && 0 <= i && to <= glyphs.length */
    for (let i = from; i < to; i++) s += glyphs[i]!.advance;
    return s;
  };
  return group(0, 2) + group(2, 5);
}
