// A tuple is a readonly array of its elements' union: a readonly view only
// reads the elements present, each at its position's type.
export function view(t: [number, string]): readonly (number | string)[] {
  return t;
}
export function prefix(
  t: [number, number, number],
): readonly [number, ...number[]] {
  return t;
}
