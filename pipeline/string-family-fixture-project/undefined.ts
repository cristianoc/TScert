// Read by pipeline/test.mts on the stand-in string-tagged family: guards on
// a value that may be `undefined` (HOST-FAMILIES.md, "Undefined arguments"),
// which TypeScript's declared parameters refuse. `isName` throws on it, so
// its `false` edge holds a unit; `isNameType` answers `false`, so its
// `true` edge holds the name's tag alone.
import {
  isName,
  isNameType,
  UnitType,
  type Unit,
} from "string-family-fixture/ast";

export function unitStart(u: Unit | undefined): number {
  return isName(u) ? u.name.length : u.start;
}

export function nameOnly(t: UnitType | undefined): UnitType.Name | undefined {
  return isNameType(t) ? t : undefined;
}

// The `false` edge of a guard answering `false` on `undefined` keeps it.
export function tagOrNone(t: UnitType | undefined): UnitType | undefined {
  return isNameType(t) ? UnitType.Name : t;
}
