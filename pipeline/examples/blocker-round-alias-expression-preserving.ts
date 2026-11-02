// Census functions:
// named-record.mts#aliasMeaning
// named-record.mts#settleDocument
// named-record.mts#settleTerm
import type { TypeTerm } from "../../tools/declaration-types.mts";
type Definition = { expression: TypeTerm | null };
export function meaning(
  d: Definition,
  record: () => Within<{ value: "keep"; store: "keep" }, boolean>,
  substitute: (t: TypeTerm) => TypeTerm,
): TypeTerm | "record" {
  if (!d.expression) throw Error("missing expression");
  if (record() && d.expression.k === "object") return "record";
  return substitute(d.expression);
}

import type { NamedRecords } from "../../tools/named-record.mts";
import type { TypeDefinition } from "../../tools/declaration-types.mts";
export function classifiers(definition: TypeDefinition): NamedRecords {
  return { definition: () => definition, record: () => true };
}
