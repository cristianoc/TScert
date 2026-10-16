/**
 * Write through an alias, then read through the original reference. Both names
 * share one Boolean cell contract; the returned value is false.
 */
function aliasWrite(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const alias: { value: boolean } = cell;
  alias.value = false;
  return cell.value;
}

/**
 * Return an assignment expression. JavaScript returns the assigned Boolean, so
 * lowering must preserve it even though the calculus write operation returns
 * null.
 */
function assignmentResult(): boolean {
  const cell: { value: boolean } = { value: true };
  return (cell.value = false);
}

/**
 * Use one assignment as the right-hand side of another. Both writes occur, and
 * the inner assignment supplies the outer assigned value.
 */
function nestedWrite(): boolean {
  const cell: { value: boolean } = { value: true };
  cell.value = cell.value = false;
  return cell.value;
}

/**
 * Mutate one shared cell in either branch. The continuation reads through the
 * same Boolean invariant after the join.
 */
function branchWrite(condition: boolean): boolean {
  const cell: { value: boolean } = { value: true };
  if (condition) {
    cell.value = false;
  } else {
    cell.value = true;
  }
  return cell.value;
}

/**
 * Allocate a cell whose invariant permits only true. Reading it justifies a
 * true result, and writing false would violate its contract.
 */
function singletonCell(): true {
  const cell: { value: true } = { value: true };
  return cell.value;
}

/**
 * An object parameter is assumed at its annotation: a reference to a
 * location whose field holds a Boolean, written and read by the same rules as
 * a cell allocated here.
 */
function externalCell(cell: { value: boolean }): boolean {
  cell.value = false;
  return cell.value;
}

/**
 * Two object parameters may be the same object. After both writes the first
 * field holds true only if they differ, so its read is Boolean: a claim that
 * it is still true is refused.
 */
function aliasedParameters(
  a: { value: boolean },
  b: { value: boolean },
): boolean {
  a.value = true;
  b.value = false;
  return a.value;
}
