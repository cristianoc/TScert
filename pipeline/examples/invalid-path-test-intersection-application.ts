// A member of the generic application operand of an intersection tested,
// then written through an alias before the read: the read is the member's
// declared `string | null`. TypeScript keeps the narrowing. Under Node the
// function returns `null` where a string is returned.
type Param<T> = { name: string; bound: T | null };

export function wrong(
  binder: Param<string> & { default: string | null },
): string {
  const alias = binder;
  if (binder.bound) {
    alias.bound = null;
    return binder.bound;
  }
  return "";
}
