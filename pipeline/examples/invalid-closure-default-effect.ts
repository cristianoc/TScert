// A function literal of no written effect whose parameter default writes a
// field its caller narrowed: a call omitting the argument runs the default,
// after which the field holds `null`, which the caller returns where it
// promises a number.
export function stale(box: { value: number | null }): number {
  const read = (n: number, reset: null = (box.value = null)): number => n;
  if (box.value !== null) {
    read(0);
    return box.value;
  }
  return 0;
}
