// Read by pipeline/test.mts on the stand-in string-tagged family:
// `isNameType` answers `false` on `undefined` (HOST-FAMILIES.md, "Undefined
// arguments"), so its `false` edge keeps `undefined`, and returning it where
// a tag is promised is refused. Under Node, `other(undefined)` returns
// `undefined`.
import { isNameType, UnitType } from "string-family-fixture/ast";

export function other(t: UnitType | undefined): UnitType {
  return isNameType(t) ? UnitType.Name : t;
}
