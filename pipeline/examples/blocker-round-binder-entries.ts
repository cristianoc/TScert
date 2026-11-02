// Census functions: array-prototype.mts#mergeRefusal,#functionPrototype,#arrayPrototype.
// A source-owned syntax term crosses the map's ordinary TypeTerm boundary.
import type { TypeTerm } from "../../tools/declaration-types.mts";
import { termText } from "../../tools/named-record.mts";
export function entries(): string {
  const binders = new Map<string, TypeTerm>([
    ["T", { k: "atom", name: "number", span: [0, 0] }],
  ]);
  return JSON.stringify(
    [...binders.entries()].map(([name, type]) => [name, termText(type)]),
  );
}
