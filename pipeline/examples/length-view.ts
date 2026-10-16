// A view of `length` admits an array, whose `length` is its store's: the read
// tests the object, and reads an array's store length or another object's own
// `length`.
export function lengthOf(x: { readonly length: number }): number {
  return x.length;
}

// A pattern reads `length` as a member access does.
export function patternLength(x: { readonly length: number }): number {
  const { length } = x;
  return length;
}

export function lengths(xs: number[]): number {
  return (
    lengthOf(xs) +
    lengthOf({ length: 3 }) +
    lengthOf([1, 2]) +
    patternLength(xs)
  );
}

// A push through the array changes the length the view reads.
export function grown(seed: number): number {
  const items = [seed];
  const view: { readonly length: number } = items;
  items.push(seed);
  return view.length;
}
