// The caller contract requires a stated string-keyed field to be an own
// enumerable property, and states no such requirement of a symbol-keyed one:
// an own non-enumerable symbol property meets `{ [sym]: number }`, and a
// spread omits it, so the copy meets neither arm of the result.
const sym: unique symbol = Symbol("sym");

export function symbolBranch(
  x: { [sym]: number } | { b: string },
): { [sym]: number } | { b: string } {
  return { ...x };
}
