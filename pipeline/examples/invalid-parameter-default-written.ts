// A written parameter with a default is a cell whose contract is its
// annotation: a string is no number (TypeScript rejects the write too).
export function write(a: number = 0): number {
  // @ts-expect-error a string is not a number
  a = "x";
  return 0;
}
