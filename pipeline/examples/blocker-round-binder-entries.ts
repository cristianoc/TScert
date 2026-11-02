// Census functions: array-prototype.mts#mergeRefusal,#functionPrototype,#arrayPrototype.
// A source-owned syntax term crosses the map's ordinary TypeTerm boundary.
import type { TypeTerm } from "../../tools/declaration-types.mts";
type ContractData =
  | null
  | undefined
  | boolean
  | number
  | string
  | readonly ContractData[]
  | { readonly [key: string]: ContractData };
export function entries(): ContractData {
  const binders = new Map<string, TypeTerm>([
    ["T", { k: "atom", name: "number", span: [0, 0] }],
  ]);
  return [...binders.entries()];
}
