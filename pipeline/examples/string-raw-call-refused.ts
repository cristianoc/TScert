// `String.raw` called rather than used as a tag: the overlay reads it only
// as a tag, so the call is refused.
export function joined(): string {
  return String.raw({ raw: ["a", "b"] }, 1);
}
