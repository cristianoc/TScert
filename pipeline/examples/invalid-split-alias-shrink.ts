// An alias shrinks the result: `alias.pop()` may leave no element, so the
// result takes the general form and element 0 may be undefined.
export function first(text: string): string {
  const cells = text.split(",");
  const alias = cells;
  alias.pop();
  return cells[0];
}
