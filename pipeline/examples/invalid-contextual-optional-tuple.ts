// A closure parameter TypeScript types from its context as a tuple with an
// optional position: TypeScript gives that position's type with `undefined`
// whether or not the annotation wrote it, so the tuple is not read, and the
// parameter needs an annotation.
export function second(
  each: (f: (row: [string, number?]) => number) => number,
): number {
  return each((row) => row[1] ?? 0);
}
