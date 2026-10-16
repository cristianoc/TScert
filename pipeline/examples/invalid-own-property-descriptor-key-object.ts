// The key of `Object.getOwnPropertyDescriptor(o, k)` is converted by
// ToPropertyKey, which calls an object's own `toString`, client code that
// here writes `seen.value`: the key is stated at a string, number or symbol.
export function wrong(
  o: object,
  k: { toString(): string },
  seen: { value: 0 },
): 0 {
  // @ts-expect-error TypeScript refuses the object too
  Object.getOwnPropertyDescriptor(o, k);
  return seen.value;
}
