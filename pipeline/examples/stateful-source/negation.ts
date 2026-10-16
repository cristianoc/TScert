/**
 * Reverse the refinements of a Boolean test. Falling through if (!flag)
 * establishes flag is true, justifying the singleton result.
 */
function negatedBranch(flag: boolean): true {
  if (!flag) {
    return true;
  }
  return flag;
}

/**
 * Check that two negations preserve the original branch polarity. On the
 * falling-through path flag is false.
 */
function doubleNegatedBranch(flag: boolean): false {
  if (!!flag) {
    return false;
  }
  return flag;
}

/**
 * Apply reversed Boolean refinements inside a closure body. Both paths
 * establish the declared true result.
 */
function negatedClosure(flag: boolean): true {
  const choose: (x: boolean) => true = (x: boolean): true => {
    if (!x) {
      return true;
    }
    return x;
  };
  return choose(flag);
}

/**
 * Negate a callback result while evaluating the callback exactly once. It
 * toggles a cell, so duplicating the call would change the final read.
 */
function negatedCall(): boolean {
  const cell: { value: boolean } = { value: false };
  const toggle: (x: null) => boolean = (x: null): boolean => {
    const before: boolean = cell.value;
    cell.value = !before;
    return before;
  };
  const result: boolean = !toggle(null);
  return cell.value;
}

/**
 * Retest a negated callback result after continue. The body sets the cell to
 * true, making the next negated condition false.
 */
function negatedLoop(): boolean {
  const cell: { value: boolean } = { value: false };
  const test: (x: null) => boolean = (x: null): boolean => cell.value;
  while (!test(null)) {
    cell.value = true;
    continue;
  }
  return cell.value;
}

/**
 * Negate a singleton-typed closure argument. The calculus can use its known
 * true value; this example keeps the broader Boolean result.
 */
function singletonClosure(): boolean {
  const flip: (x: true) => boolean = (x: true): boolean => !x;
  return flip(true);
}

/**
 * Negate a call whose result is known to be true but which also writes a cell.
 * Selecting the known result must not skip that write; the final read is
 * false.
 */
function effectfulSingletonCondition(): boolean {
  const cell: { value: boolean } = { value: true };
  const clear: (x: null) => true = (x: null): true => {
    cell.value = false;
    return true;
  };
  const result: boolean = !clear(null);
  return cell.value;
}
