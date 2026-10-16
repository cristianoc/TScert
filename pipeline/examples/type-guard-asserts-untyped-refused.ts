// `asserts x` without a type promises the argument truthy, which names no
// type of the fragment.
export function check(x: unknown): asserts x {
  if (!x) throw Error("falsy");
}
