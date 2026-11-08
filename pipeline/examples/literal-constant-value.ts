// pretext's segmentAtLineBreaks: a module constant whose type is one safe
// integer's literal (`const TEXT = 0`) holds that integer, so a binding
// assigned it is known to be that integer, and a loop invariant bounding the
// last kind by the segments' count keeps the last segment present.
export const TEXT = 0;

/** @ensures safeInteger(result) && result >= 0 && result <= 15 */
function kindOf(code: number): number {
  if (code === 0x20) return 1;
  return TEXT;
}

export function marks(codes: number[]): number[] {
  const flags: number[] = [];
  let lastKind = -1;
  /** @invariant safeInteger(lastKind) && lastKind < 16 * flags.length */
  for (let i = 0; i < codes.length; i++) {
    const kind = kindOf(codes[i]!);
    if (kind === lastKind) {
      flags[flags.length - 1] = flags[flags.length - 1]! | 0x80;
      continue;
    }
    if (kind === 1) {
      flags.push(TEXT);
      lastKind = TEXT;
      continue;
    }
    flags.push(kind);
    lastKind = kind;
  }
  return flags;
}
