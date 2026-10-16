// A write nested in a larger expression keeps the binding in a cell: the
// lowering types the rest of the statement at the frame it entered with,
// which a slot rebound within it would not fit. As a cell, `x` is read at
// what the write stored.
export function nestedSum(): number {
  let x: number = 0;
  const z = (x = 1) + x;
  return z + x;
}
