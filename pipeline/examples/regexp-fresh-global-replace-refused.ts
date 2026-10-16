// A callback replacing through a global regex literal: each call allocates
// the regex and writes only its `lastIndex`, a location the call allocated,
// so the callback preserves the heap it was called with. The call of
// `[Symbol.replace]` itself writes an existing location, the regex's, and
// no effect states that the location is the call's own: the callback is not
// certified, and `map`'s result is sparse.
export function collapsed(lines: string[]): string[] {
  return lines.map((l) => l.replace(/\s+/g, " "));
}
