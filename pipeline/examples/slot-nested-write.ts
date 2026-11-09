// A write nested in a larger expression rebinds the binding's slot where it
// runs (SOURCE-ELABORATION.md, "Slot or cell"): the rest of the statement
// reads `x` at what the write stored.
export function nestedSum(): number {
  let x: number = 0;
  const z = (x = 1) + x;
  return z + x;
}
