// Equality compares the field value saved before its right operand writes.
export function comparedBeforeWrite(box: { value: number | null }): boolean {
  return box.value !== (box.value = null);
}

// The saved comparison does not establish the field's current contents.
export function currentAfterWrite(box: {
  value: number | null;
}): number | null {
  if (box.value !== (box.value = null)) {
    return box.value;
  }
  return 0;
}
