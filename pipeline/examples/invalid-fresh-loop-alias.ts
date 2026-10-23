// A fresh object stored in a variable an earlier statement declared is the
// object that variable holds: the write through it changes the field the
// test narrowed. The returned value is null.
export function loopAlias(n: number): number {
  let last: { value: number | null } = { value: 0 };
  for (let i = 0; i < n; i++) {
    const next: { value: number | null } = { value: i };
    if (next.value === null) return 0;
    last = next;
    last.value = null;
    return next.value;
  }
  return last.value ?? 0;
}
