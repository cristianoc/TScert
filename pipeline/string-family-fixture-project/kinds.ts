// The stand-in family's tag enum read as a value (HOST-FAMILIES.md,
// "Activation"): its members are those of the runtime object the stand-in's
// entry point exports, so a test of the tag against a constant narrows, and
// a constant has its literal type. pipeline/test.mts also runs these over a
// copy whose runtime enum differs from its declaration, where they are
// refused.
import { UnitType, type Unit } from "string-family-fixture/ast";

export function nameOf(u: Unit): string {
  return u.type === UnitType.Name ? u.name : "";
}

export function literalTag(): "literal" {
  return UnitType.Literal;
}
