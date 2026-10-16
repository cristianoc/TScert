/**
 * First-order generic aliases. Applying Id or Box is substitution, not a
 * second type: Id<T> is T, and Box<T> is a cell of T.
 */
type Id<T> = T;
type Box<T> = { value: T };

function wrap(x: Id<boolean>): Id<boolean> {
  return x;
}

function id<T>(x: Id<T>): Id<T> {
  return x;
}

function readBox(): boolean {
  const cell: Box<boolean> = { value: true };
  return cell.value;
}
