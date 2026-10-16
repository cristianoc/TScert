// A call between the write and the default may write the cell: TypeScript
// keeps `value` narrowed to `number` across `set()`, which stores a string.
// The default's read is at the cell's contract, `number | string`.
export function clobbered(): number {
  let value: number | string = 0;
  const set = (): void => {
    value = "s";
  };
  value = 1;
  let a: number = 0;
  [a = (set(), value)] = [undefined];
  return a;
}
