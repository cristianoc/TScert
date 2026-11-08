// pretext analysis.ts: segmentAtLineBreaks tests `normalized[i] ?? missing()`
// inside the loop that pushes its segments' starts and flags. An index read
// of a string reads no location, so the statement keeps every fact over
// lengths, and the loop keeps `starts.length === flags.length`.

function missing(): never {
  throw new RangeError("missing value");
}

/** @ensures result.starts.length === result.flags.length */
export function marks(text: string): { starts: number[]; flags: number[] } {
  const starts: number[] = [];
  const flags: number[] = [];
  /** @invariant starts.length === flags.length */
  for (let i = 0; i < text.length; i++) {
    if ((text[i] ?? missing()) === " ") continue;
    starts.push(i);
    flags.push(text.charCodeAt(i) & 15);
  }
  return { starts, flags };
}
