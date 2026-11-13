// The facts after a block are its statements' (its own bindings left out),
// and after a choice what both arms establish: a loop's written invariant
// (`starts.length === flags.length`) reaches the loops after it, across a
// loop and a choice that write elements of `flags` at indices below its
// length (pretext's `segmentAtLineBreaks`).
export function texts(s: string): number {
  const starts: number[] = [];
  const flags: number[] = [];
  /** @invariant starts.length === flags.length */
  for (let i = 0; i < s.length; i++) {
    if (s.charCodeAt(i) === 32) continue;
    starts.push(i);
    flags.push(1);
  }
  let has = false;
  const count = flags.length;
  /** @invariant safeInteger(j) && safeInteger(count) && j + 2 <= count && count === flags.length */
  for (let j = count - 2; j >= 0; j--) {
    if (flags[j]! === 2) continue;
    flags[j + 1] = flags[j + 1]! | 4;
    has = true;
  }
  if (has) for (let j = 0; j < count; j++) if ((flags[j]! & 4) === 0) flags[j] = flags[j]! | 8;
  const out: string[] = [];
  /** @invariant safeInteger(j) && safeInteger(count) && out.length === j && count === flags.length && starts.length === flags.length */
  for (let j = 0; j < count; j++) out.push(s.slice(starts[j], j + 1 < count ? starts[j + 1] : s.length));
  return out.length;
}
