// A function of the host package declaring a predicate that the guard table
// does not list is read without its predicate (HOST-FAMILIES.md, "Guard
// recognition"), the sync API's `isUnionType` among them: the `true` edge
// does not narrow `type` to a union, which alone states `getTypes`.
import { isUnionType, type Type } from "typescript/unstable/sync";

export function parts(type: Type): readonly Type[] {
  return isUnionType(type) ? type.getTypes() : [type];
}
