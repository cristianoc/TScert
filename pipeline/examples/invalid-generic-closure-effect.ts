// A generic closure's write ends its caller's narrowing of the field it
// writes: after the call the field holds `null`, which the function returns
// where it promises a number.
export function stale(box: { value: number | null }): number {
  const reset = <T>(x: T): T => {
    box.value = null;
    return x;
  };
  if (box.value !== null) {
    reset(0);
    return box.value;
  }
  return 0;
}
