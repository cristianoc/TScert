/**
 * Write through an alias and break immediately. The break edge must reach the
 * post-loop read with the cell contract intact.
 */
function stopAfterWrite(): boolean {
  const cell: { value: boolean } = { value: true };
  const test: (x: null) => boolean = (x: null): boolean => cell.value;
  while (test(null)) {
    const alias: { value: boolean } = cell;
    alias.value = false;
    break;
  }
  return cell.value;
}

/**
 * Write through an alias and continue to the condition. The next test must see
 * false; continue must not jump straight into the body.
 */
function continueAfterWrite(): boolean {
  const cell: { value: boolean } = { value: true };
  const test: (x: null) => boolean = (x: null): boolean => cell.value;
  while (test(null)) {
    const alias: { value: boolean } = cell;
    alias.value = false;
    continue;
  }
  return cell.value;
}

/**
 * Break only the inner loop. Control then reaches the outer body return,
 * rather than escaping both loops.
 */
function nestedBreak(flag: boolean): boolean {
  while (flag) {
    while (flag) {
      const local: boolean = flag;
      break;
    }
    return true;
  }
  return false;
}

/**
 * Choose between continue and break inside a loop. The true path writes false
 * and retests; the false path exits without that write.
 */
function branchContinue(flag: boolean): boolean {
  const cell: { value: boolean } = { value: true };
  const test: (x: null) => boolean = (x: null): boolean => cell.value;
  while (test(null)) {
    if (flag) {
      cell.value = false;
      continue;
    }
    break;
  }
  return cell.value;
}
