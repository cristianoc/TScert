// Pretext getTerminalLetterSpacing/normalizePreparedLineStart: aliases and mutable loop bindings.
/** @invariant this.flags.length === this.widths.length */
type Prepared = { flags: Uint8Array; widths: number[] };
/**
 * @requires safeInteger(index) && 0 <= index && index <= prepared.widths.length
 * @requires safeInteger(grapheme) && (grapheme <= 0 || index < prepared.widths.length)
 */
export function terminal(
  prepared: Prepared,
  index: number,
  grapheme: number,
): number {
  const { flags } = prepared;
  if (grapheme > 0) return flags[index]!;
  return 0;
}
/** @requires safeInteger(start) && 0 <= start && start < xs.length */
export function scan(xs: number[], start: number): number {
  let i = start;
  /** @invariant safeInteger(i) && 0 <= i && i < xs.length */
  while (true) {
    const value = xs[i]!;
    if (value > 0) return value;
    if (++i >= xs.length) return 0;
  }
}
