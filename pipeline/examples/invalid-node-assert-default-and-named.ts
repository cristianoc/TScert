// A default import beside named bindings is read as the default import
// alone is: a mention other than a call or a member's call is refused.
import assert, { type AssertPredicate } from "node:assert/strict";

export function checker(): (value: unknown) => void {
  const check = assert;
  return (value: unknown) => check(value, "a value");
}
export type Predicate = AssertPredicate;
