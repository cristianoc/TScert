// An array's `length` is a number, not the literal a closure's result names.
export function length(): 2 {
  const f = (xs: readonly number[]): 2 => xs.length;
  return f([1, 2]);
}
