// A prefix cursor advances twice: the counter's loop invariant fails.
export function invalidCursor(items: Int32Array): number {
  const size = items.length;
  let n = 0;
  /** @invariant safeInteger(n) && 0 <= n && n <= items.length */
  while (n < size) {
    const value = items[n++]!;
    n++;
  }
  return items[n - 1]!;
}
