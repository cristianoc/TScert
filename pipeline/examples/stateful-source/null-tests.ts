/** Test null membership in a primitive union without assuming a refinement. */
function isNull(value: null | boolean): boolean {
  return value === null;
}

/** Put the null literal first; operand order must still be respected. */
function nullFirst(value: null | boolean): boolean {
  return null === value;
}

/** Negate the null test using strict inequality. */
function isPresent(value: null | boolean): boolean {
  return value !== null;
}

/** Perform a null test inside a callback with a union argument contract. */
function nullableCallback(value: null | boolean): boolean {
  const test: (x: null | boolean) => boolean = (x: null | boolean): boolean =>
    x === null;
  return test(value);
}

/** The operand mutates a cell and returns null; equality must call it once. */
function effectfulNullTest(): boolean {
  const cell: { value: boolean } = { value: false };
  const toggle: (x: null) => null = (x: null): null => {
    const before: boolean = cell.value;
    cell.value = !before;
    return null;
  };
  const result: boolean = toggle(null) === null;
  return cell.value;
}

/** Strict inequality also works with the null literal on the left. */
function nullNotFirst(value: null | boolean): boolean {
  return null !== value;
}
