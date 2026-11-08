// pretext line-text.ts buildRangeText: a bounded segment read in the if
// arm after a short-circuit condition and a continue.
export function buildRangeText(
  segments: readonly string[],
  start: number,
): string {
  let text = "";
  for (let i = 0; i < segments.length; i++) {
    const kind = i & 7;
    if (
      kind === 1 ||
      kind === 2 ||
      ((kind === 3 || kind === 4) && segments[i]!.charCodeAt(0) === 173)
    )
      continue;
    if (i === start) {
      text += segments[i]!.slice(1);
    } else {
      text += segments[i]!;
    }
  }
  return text;
}
