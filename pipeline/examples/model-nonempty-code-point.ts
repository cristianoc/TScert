// A nonempty filtered string needs a defined code point at position zero.
// Model study: 2 Sonnet samples (code-point-of-nonempty-string.ts).
export function initials(name: string): number[] {
  return name
    .split(/\s+/)
    .filter((part) => part.length > 0)
    .map((part) => part.codePointAt(0) as number);
}
