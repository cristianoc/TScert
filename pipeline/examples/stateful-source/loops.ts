/**
 * Exercise a loop invariant with an immutable condition. False skips the body;
 * true loops forever. Verification establishes type safety, not termination.
 */
function zeroTrips(flag: boolean): boolean {
  while (flag) {
    const local: boolean = flag;
  }
  return flag;
}

/**
 * Retest a captured cell on every iteration. The alias write makes the next
 * condition false, so this loop performs one write and returns false.
 */
function oneWrite(): boolean {
  const cell: { value: boolean } = { value: true };
  const test: (x: null) => boolean = (x: null): boolean => cell.value;
  while (test(null)) {
    const alias: { value: boolean } = cell;
    alias.value = false;
  }
  return cell.value;
}

/**
 * Exercise nested loop heads and an early return from the inner body. Both
 * Boolean inputs terminate, returning the input value.
 */
function nested(flag: boolean): boolean {
  while (flag) {
    while (flag) {
      return flag;
    }
  }
  return flag;
}
