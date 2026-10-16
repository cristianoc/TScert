// A local cell whose contract is a union of records: each arm is an
// invariant cell, one holding `null | boolean` and one holding only `null`.
// A closure captures it and reads its field when called, after the writes
// that precede the call; a write of `null` fits both arms.

type Cell = { value: null | boolean } | { value: null };

/** The captured cell is read when the closure runs. */
function readLater(): null | boolean {
  const cell: Cell = { value: null };
  const read = (unit: null): null | boolean => cell.value;
  return read(null);
}

/** The same read as the closure's one statement. */
function readBlock(): null | boolean {
  const cell: Cell = { value: null };
  const read = (unit: null): null | boolean => {
    return cell.value;
  };
  return read(null);
}

/** The closure writes `null`, which both arms admit, then reads. */
function writeThenRead(): null | boolean {
  const cell: Cell = { value: null };
  const touch = (unit: null): null | boolean => {
    cell.value = unit;
    return cell.value;
  };
  return touch(null);
}

/** A cell of the union arrives as a parameter, at its annotation. */
function external(cell: Cell): null | boolean {
  const read = (unit: null): null | boolean => cell.value;
  return read(null);
}
