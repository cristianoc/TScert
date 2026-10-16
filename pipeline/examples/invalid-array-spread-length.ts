// A copy of an array holds its own enumerable properties, its elements and
// any field it carries; its `length` is not one, where TypeScript types the
// copy as having it.
export function count(xs: number[]): number {
  const copy: { length: number } = { ...xs };
  return copy.length;
}
