// A function literal of no written effect whose parameter default writes a
// field its caller narrowed: the default runs at a call omitting its
// argument, so the literal's effect is its default's write, and the caller
// tests the field again after the call.
export function reread(box: { value: number | null }): number {
  const read = (n: number, reset: null = (box.value = null)): number => n;
  if (box.value !== null) {
    const kept = read(box.value);
    return box.value === null ? kept : box.value;
  }
  return 0;
}
