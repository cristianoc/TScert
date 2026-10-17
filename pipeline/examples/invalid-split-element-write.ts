// A write through an alias may store `undefined` where element 0 was: the
// result takes the general form and element 0 may be undefined.
export function first(text: string, value: string | undefined): string {
  const cells: (string | undefined)[] = text.split(",");
  cells[0] = value;
  return cells[0];
}
