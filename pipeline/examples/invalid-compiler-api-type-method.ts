// A `this is X` method of the sync API's `Type` is no member of its named
// view (COMPILER-API.md, reading rule 4): its promise is about the receiver,
// which is no actual of the call, so `isUnionType` is read through the
// stated guard of that name instead (`compiler-api-stated-guards`).
import { type Type } from "typescript/unstable/sync";

export function parts(type: Type): readonly Type[] {
  return type.isUnionType() ? type.getTypes() : [type];
}
