// The stand-in family's allocating member (HOST-FAMILIES.md, "The family
// contract"): under a description listing `Unit.notes` as allocating, no
// shape states it and this read is refused; under one that does not, it is
// a required member and the read verifies.
import type { Unit } from "string-family-fixture/ast";

export function notesOf(u: Unit): readonly string[] {
  return u.notes;
}
