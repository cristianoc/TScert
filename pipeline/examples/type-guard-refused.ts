// A user-defined type guard promises that a `true` result leaves its
// argument a `T`: a relation between the result and the argument, which no
// function type states, so a caller has nothing to narrow by.
function isString(x: string | number): x is string {
  return typeof x === "string";
}

export function length(x: string | number): number {
  return isString(x) ? x.length : x;
}
