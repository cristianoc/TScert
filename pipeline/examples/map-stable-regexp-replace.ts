// A callback replacing through a global regex literal: each call allocates
// the regex, and `[Symbol.replace]` writes its `lastIndex`, a location
// holding a number, which changes no array: `map`'s result is dense.
export function collapsed(lines: string[]): string[] {
  return lines.map((l) => l.replace(/\s+/g, " "));
}
