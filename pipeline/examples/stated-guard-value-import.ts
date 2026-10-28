// An imported type guard stating the empty footprint at its promise's type
// (`s is Within<F, Circle>`), whose module's run certifies it: functions
// stating that no value changes call it, one reading the radius on its true
// edge; a guard of this file stating its effect alike is called the same way.
// Census functions:
// fragment-expressions.mts#resolve, fragment-expressions.mts#moduleFunction,
// fragment-expressions.mts#inertRead, fragment-statements.mts#typeStatement.
import { isCircle, type Circle, type Square } from "@fixture/stated";

export function circular(
  s: Circle | Square,
): Within<{ value: "keep"; store: "keep" }, boolean> {
  return isCircle(s);
}

export function radius(
  s: Circle | Square,
): Within<{ value: "keep"; store: "keep" }, number> {
  return isCircle(s) ? s.radius : 0;
}

// A guard of this file stating its effect alike, certified by its own unit.
export function isSquare(
  s: Circle | Square,
): s is Within<{ value: "keep"; store: "keep" }, Square> {
  return s.kind === "square";
}

export function side(
  s: Circle | Square,
): Within<{ value: "keep"; store: "keep" }, number> {
  return isSquare(s) ? s.side : 0;
}

// A guard no code calls, certified at its statement whatever its callers.
export function isUnit(
  s: Circle | Square,
): s is Within<{ value: "keep"; store: "keep" }, Circle> {
  return s.kind === "circle" && s.radius === 1;
}
