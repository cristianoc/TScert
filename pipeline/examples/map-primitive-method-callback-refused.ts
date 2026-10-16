// A callback calling a string's method changes no location, but its effect
// is not certified: the primitives' prototype members carry none, and the
// effect inference admits no call of a member read off a primitive. So
// `map` takes the unrestricted overload, whose result is sparse, and no
// readable `string[]` is derived.
export function trimmed(lines: string[]): string[] {
  return lines.map((l: string): string => l.trim());
}
