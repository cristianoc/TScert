// Assigning one parameter must not lose an unrelated short-circuit refinement.
function unrelatedFact(value: number | null, other: number | null): number {
  if (other !== null && (value = null) === null) {
    return other;
  }
  return 0;
}

// Both cells are private; replacing one parameter leaves the other unchanged.
function independentParameters(
  left: boolean,
  keep: boolean,
  right: boolean,
): boolean {
  left = !left;
  right = !right;
  return keep ? left : right;
}

// Closures share a parameter's location, whereas a const keeps its value.
function capturedParameter(value: boolean): boolean {
  const snapshot = value;
  const read = (): boolean => value;
  const reset = (): null => {
    value = false;
    return null;
  };
  const done = reset();
  return snapshot && !read();
}
