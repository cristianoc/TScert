// A positive length test needs to justify the read at length minus one.
// Model study: 2 Sonnet samples (last-element-after-length-test.ts and
// last-element-in-conditional.ts, 1 each).
export function lastWord(s: string): string {
  const words = s.split(/\s+/).filter((w) => w.length > 0);
  return words.length > 0 ? words[words.length - 1] : "";
}
