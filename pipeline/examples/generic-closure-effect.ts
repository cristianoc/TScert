// A generic closure that writes the heap is claimed at an effect covering
// the write: its caller tests the written field again after the call.
export function reread(box: { value: number | null }): number {
  const reset = <T>(x: T): T => {
    box.value = null;
    return x;
  };
  if (box.value !== null) {
    const kept = reset(box.value);
    return box.value === null ? kept : box.value;
  }
  return 0;
}
