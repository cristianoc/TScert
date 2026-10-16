// The update runs after a `continue` too, here before `y` is written: the
// update's read of `y` may see null.
function staleUpdate(again: boolean, skip: boolean): number {
  let y: number | null = null;
  let total: number = 0;
  for (let i: number = 0; again; total = total + y) {
    if (skip) {
      continue;
    }
    y = 1;
  }
  return total;
}
