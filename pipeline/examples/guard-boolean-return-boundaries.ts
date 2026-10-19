// A guard's Boolean return, at its boundaries: the test runs once, its
// effects and its throws as written; a `finally` runs after the returned
// answer is fixed, and one that returns overrides it; a closure inside a
// guard returns its own value, and a guard inside a closure returns its
// truth; an arrow guard with a defaulted parameter.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function counted(v: Json, log: string[]): v is string {
  return typeof v === "string" && log.push("tested") > 0;
}
function check(v: string): boolean {
  if (v === "") throw Error("empty");
  return true;
}
export function nonEmpty(v: Json): v is string {
  return typeof v === "string" && check(v) === true;
}
export function finished(v: Json, log: string[]): v is string {
  try {
    return typeof v === "string";
  } finally {
    log.push("finally");
  }
}
export function overridden(v: Json): v is string {
  try {
    return typeof v === "string";
  } finally {
    return false;
  }
}
export function nested(v: Json): v is string {
  const positive = (n: number): boolean => n > 0;
  return typeof v === "string" && positive(v.length) === true;
}
export function guardOf(): (v: Json) => v is number {
  return (v: Json): v is number => typeof v === "number";
}
export const atLeast = (v: Json, min: number = 0): v is number =>
  typeof v === "number" && v >= min;
