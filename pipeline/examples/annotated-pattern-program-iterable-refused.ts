// An array pattern under an annotation over a program's iterable: its steps
// read the iterator, which the annotation does not state.
export function first(values: Iterable<number>): number | undefined {
  const [a]: Iterable<number> = values;
  return a;
}
