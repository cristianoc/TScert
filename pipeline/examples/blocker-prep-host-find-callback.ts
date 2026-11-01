// Census functions:
// computed-types.mts#computedType
// computed-types.mts#aliasApplication
// computed-types.mts#inexpressible
import { type Type, type Checker, isUnionType } from "typescript/unstable/sync";
import { literalUnion } from "../../tools/computed-types.mts";
export function find(checker: Checker, type: Type): string {
  const parts = isUnionType(type) ? type.getTypes() : [type];
  const part = parts.find((p) => literalUnion(p, [0, 0]) === null) ?? type;
  return checker.typeToString(part);
}
