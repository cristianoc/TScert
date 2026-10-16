// An element read and a field read change no location: what is known of a
// cell's contents before the read is known after it, in a pattern's default
// and in an expression's arm.

// The key writes the cell; the default, after the position's read, reads it.
export function keyBeforeDefault(): number {
  let value: number | null = null;
  const box: { slot: number } = { slot: 0 };
  [box[(value = 1) === 1 ? "slot" : "slot"] = value] = [undefined];
  return box.slot;
}

// A cell a closure shares, written in an earlier statement.
export function sharedCellDefault(): number {
  let value: number | null = null;
  const peek = () => value;
  value = 1;
  let a: number = 0;
  [a = value] = [undefined];
  return a + (peek() ?? 0);
}

// The right side writes the cell before the pattern reads its position.
export function rightSideWrite(): number {
  let value: number | null = null;
  let a: number = 0;
  [a = value] = [((value = 1), undefined)];
  return a;
}

// A pattern over an array a parameter holds.
export function heldArrayDefault(arr: (number | undefined)[]): number {
  let value: number | null = null;
  const peek = () => value;
  value = 1;
  let a: number = 0;
  [a = value] = arr;
  return a + (peek() ?? 0);
}

// An element read in a condition, then the cell read in an arm.
export function elementTestArm(arr: (number | undefined)[]): number {
  let value: number | null = null;
  const peek = () => value;
  value = 1;
  const z = arr[0] === undefined ? value : 0;
  return z + (peek() ?? 0);
}
