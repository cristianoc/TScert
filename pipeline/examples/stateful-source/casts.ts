// A type assertion is the operand's value; the runtime never sees it. What it
// asserts is one more obligation on the operand, never a fact about it: the
// claim at the assertion must follow from what the operand is known to be.

// After the guard the field is a number; the assertion adds nothing.
function assertedSnapshot(x: { value: number | null }): number {
  if (x.value === null) return 0;
  const value = x.value as number;
  x.value = null;
  return value;
}

// `satisfies` checks the operand and leaves its type alone.
function satisfiedSnapshot(x: { value: number | null }): number {
  if (x.value === null) return 0;
  const value = x.value satisfies number;
  x.value = null;
  return value;
}

// A non-null assertion on a value already known non-null.
function nonNullSnapshot(x: { value: number | null }): number {
  if (x.value === null) return 0;
  const value = x.value!;
  x.value = null;
  return value;
}

// Widening is an assertion the operand meets outright.
function wideningAssertion(seed: 1): number | null {
  const value = seed as number;
  return value;
}
