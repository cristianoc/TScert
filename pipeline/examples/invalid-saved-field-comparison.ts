// The left read may be a number while the right operand makes the field null.
export function wrong(box: { value: number | null }): number {
  if (box.value !== (box.value = null)) {
    return box.value;
  }
  return 0;
}
