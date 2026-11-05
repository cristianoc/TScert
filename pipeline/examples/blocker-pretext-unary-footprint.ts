// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): han-kerning.ts#getFontData.
// Refusal: reject: source expression obligation: no derivation of its
// node-typing claim, at the read of an element of the mapped array.
// A function whose result is built with a unary minus, `-m.left`, mapped
// over an array and the result read in a closure: the unary operator lowers
// to its operand's arithmetic, which changes no location, so the
// function's footprint is within the empty one and `map` gives a dense
// array of its results.
type Glyph = { advance: number; type: number };

function bounds(c: number): Glyph {
  return { advance: c, type: -c };
}

export function fontData(): number {
  const glyphs = [0x3001, 0x3002].map((c) => bounds(c));
  const group = (i: number): number => glyphs[i]?.type ?? 0;
  return group(0);
}
