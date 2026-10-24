// Read by pipeline/test.mts on the stand-in string-tagged family:
// `isNameOrAbsent` answers `true` on `undefined`, outside the recognition
// contract, so its table has no entry and it narrows nothing: its declared
// promise would return `undefined` as a name. Under Node, `named(undefined)`
// returns `undefined`.
import {
  isNameOrAbsent,
  type Name,
  type Unit,
} from "string-family-fixture/ast";

export function named(u: Unit | undefined): Name | null {
  return isNameOrAbsent(u) ? u : null;
}
