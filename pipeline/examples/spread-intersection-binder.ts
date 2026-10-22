// A spread of an intersection with a type parameter operand: the copy is the
// meet of the instance with the record, known only at an instance.
export function copied<T extends { a: number }>(
  x: T & { b: string },
): { a: number; b: string } {
  return { ...x };
}
