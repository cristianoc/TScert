// Read by pipeline/test.mts on the stand-in string-tagged family: a guard of
// one tag and one through a helper of its tag narrow both edges, their tags
// the family's string constants.
import { isExpression, isName, type Unit } from "typescript/ast";

export function name(n: Unit): string {
  return isName(n) ? n.name : "";
}

export function notName(n: Unit): number {
  if (!isName(n)) return n.start;
  return n.name.length;
}

export function expression(n: Unit): number {
  if (isExpression(n)) return n.start;
  return n.value.length;
}
