// A write of `true` fits the `null | boolean` arm of the cell's union but not
// the arm holding only `null`: the cell may be of that arm, so the write's
// obligation fails, though TypeScript admits it.

type Cell = { value: null | boolean } | { value: null };

function writeTrue(): null | boolean {
  const cell: Cell = { value: null };
  const touch = (unit: null): null | boolean => {
    cell.value = true;
    return cell.value;
  };
  return touch(null);
}
