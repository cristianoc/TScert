// An assertion function promises that a normal completion leaves its
// argument a `T`: a relation between the completion and the argument, which
// no function type states.
function assertString(x: string | number): asserts x is string {
  if (typeof x !== "string") throw new Error("not a string");
}

export function length(x: string | number): number {
  assertString(x);
  return x.length;
}
