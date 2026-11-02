// A record classifier's preservation contract is checked at its definition.
import type { NamedRecords } from "../../tools/named-record.mts";
import type { TypeDefinition } from "../../tools/declaration-types.mts";
export function invalid(definition: TypeDefinition): NamedRecords {
  return {
    definition: () => definition,
    record: () => {
      definition.expression = null;
      return true;
    },
  };
}
