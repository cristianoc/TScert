// A member of an intersection's operand tested, then a call before the
// read: the member is writable, so no stable link keeps it past the call,
// and the read is the member's declared `string | null`. TypeScript keeps
// the narrowing. Under Node a call clearing the member makes the function
// return `null` where a string is returned.
type Param<T> = { name: string; bound: T | null };

export function wrong(
  binder: Param<number> & { default: string | null },
  clear: () => void,
): string {
  if (binder.default) {
    clear();
    return binder.default;
  }
  return "";
}
