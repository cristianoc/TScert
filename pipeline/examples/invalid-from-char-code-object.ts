// `String.fromCharCode(o)` converts an object by its own `valueOf`, client
// code that here writes `seen.value`: each argument is stated at the
// primitives.
export function wrong(o: { valueOf(): number }, seen: { value: 0 }): 0 {
  // @ts-expect-error TypeScript refuses the object too
  String.fromCharCode(o);
  return seen.value;
}
