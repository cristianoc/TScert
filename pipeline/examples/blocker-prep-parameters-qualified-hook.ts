// Census functions:
// declaration-graph.mts#closeDeclarations
// declaration-graph.mts#collectFrom
// declaration-graph.mts#collectInstances
// declaration-graph.mts#collect
// declaration-graph.mts#elaborateDeclaration
type Hook = (
  n: number,
  read: (n: number) => Modifies<{ values: "any"; stores: "grow" }, string>,
) => Modifies<{ values: "any"; stores: "grow" }, string>;
export function invoke(hook: Hook, ...args: Parameters<Hook>): string {
  return hook(...args);
}
