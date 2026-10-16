// `Math.max(o)` converts an object by its own `valueOf`, client code that
// here writes `seen.value`: each argument is stated at the primitives.
export function wrong(o: { valueOf(): number }, seen: { value: 0 }): 0 {
  // @ts-expect-error TypeScript refuses the object too
  Math.max(o);
  return seen.value;
}
