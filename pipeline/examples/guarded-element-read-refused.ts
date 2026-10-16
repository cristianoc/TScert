// Element reads the code guards: a nonzero length makes the last position
// present, and a test that an element is defined makes a second read of it
// the same value. Neither guard is carried to the read.
export function trimEnd(out: string[]): string[] {
  while (out.length && !out[out.length - 1].trim()) out.pop();
  return out;
}

export function firstKnown(xs: string[], known: Set<string>): boolean {
  return xs[0] !== undefined && known.has(xs[0]);
}
