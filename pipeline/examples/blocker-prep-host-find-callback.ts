// Census functions:
// computed-types.mts#computedType
// computed-types.mts#aliasApplication
// computed-types.mts#inexpressible
import { type Type, type Checker, isUnionType } from "typescript/unstable/sync";
import { literalUnion } from "../../tools/computed-types.mts";
export function find(checker: Checker, type: Type): string {
  const parts = isUnionType(type) ? type.getTypes() : [type];
  for (const candidate of parts) {
    if (literalUnion(candidate, [0, 0]) === null) {
      return checker.typeToString(candidate);
    }
  }
  return checker.typeToString(type);
}
