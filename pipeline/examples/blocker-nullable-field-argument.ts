// A recursive traversal needs the tested nullable field read to meet its
// recursive value contract.
// Census functions:
// declaration-graph.mts#externalStatements,
// declaration-graph.mts#promisedBinders,
// declaration-graph.mts#promisedMethods, declaration-graph.mts#promisedNames,
// fragment-support.mts#completes.
import type { TypeTerm } from "../../tools/declaration-types.mts";
export function use(type: TypeTerm): void {
  const visit = (t: TypeTerm): void => {
    switch (t.k) {
      case "function":
      case "constructor":
        for (const p of t.params) visit(p);
        if (t.rest) visit(t.rest);
        visit(t.result);
        return;
      default:
        return;
    }
  };
  visit(type);
}
