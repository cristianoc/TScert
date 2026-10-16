// A closure may run before the cell it captures is assigned: here it does,
// and returns `undefined`. TypeScript does not check definite assignment
// inside a closure and accepts this; the closure reads the cell at its
// contract, `string | undefined`.
function capturedBeforeAssignment(): string {
  let x: string;
  const read = (): string => x;
  const early = read();
  x = "a";
  return early;
}
