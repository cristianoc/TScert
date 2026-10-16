// A rest typed by an intersection states a contract that can be empty at an
// instance TypeScript admits: at `T := boolean`, no array is both a writable
// `boolean[]` and a `number[]`, yet TypeScript accepts the call with no
// actuals. A body writing through one operand's view then returns a number as
// a `boolean`.
type NumbersOrStrings = number[] | string[];
function first<T>(...xs: T[] & NumbersOrStrings): T {
  (xs as number[]).push(1);
  const result = xs[0];
  if (result === undefined) throw "empty";
  return result;
}
export function wrong(): boolean {
  return first<boolean>();
}
