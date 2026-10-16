// A `break` in the middle of a clause leaves the switch with what the cell
// held there: `y` may still be null after it.
function midBreak(x: number, c: boolean): number {
  let y: number | null = null;
  switch (x) {
    case 1:
      if (c) {
        break;
      }
      y = 2;
      break;
    default:
      y = 3;
  }
  const z: number = y;
  return z;
}
