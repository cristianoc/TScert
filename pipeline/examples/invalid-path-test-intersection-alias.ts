// A member of an intersection's operand tested, then written through an
// alias before the read: the write ends the read link, so the read is the
// member's declared `string | null`. TypeScript keeps the narrowing. Under
// Node the function returns `null` where a string is returned.
type Param<T> = { name: string; bound: T | null };

export function wrong(
  binder: Param<number> & { default: string | null },
): string {
  const alias = binder;
  if (binder.default) {
    alias.default = null;
    return binder.default;
  }
  return "";
}
