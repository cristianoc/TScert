// A copy of a class value holds its static fields at their types: a number
// static is not a string field of the copy.
class StaticReader {
  static readonly value: number = 1;
}

export function copyStaticData(): { value: string } {
  // @ts-expect-error a number field is not a string field
  return { ...StaticReader };
}
