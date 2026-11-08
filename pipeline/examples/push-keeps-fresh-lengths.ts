// pretext's `segmentAtLineBreaks`: two arrays built by literals grow
// together, one element each per step, while the loop writes a typed array
// between the pushes. An array literal's store field is apart from the store
// fields of the older arrays in its scope whatever the heap holds, so a push
// into either keeps the other's length, and the two stay equally long.

/** @invariant this.starts.length === this.flags.length */
export type Segments = { starts: number[]; flags: number[] };

export function segments(text: string, breaks: Uint8Array): Segments {
  const starts: number[] = [];
  const flags: number[] = [];
  /** @invariant starts.length === flags.length */
  for (let i = 0; i < text.length; i++) {
    if (i < breaks.length) breaks[i] = 1;
    if (text.charCodeAt(i) === 32) continue;
    starts.push(i);
    flags.push(breaks[i] ?? 0);
  }
  return { starts, flags };
}
