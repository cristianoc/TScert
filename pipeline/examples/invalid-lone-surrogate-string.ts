// A string holding a lone surrogate is no well-formed Unicode string: the
// wire carries no such string as itself, and the gate refuses it.
export function lone(): string {
  return "\uD800";
}
