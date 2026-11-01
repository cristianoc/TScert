// Census functions:
// declaration-graph.mts#closeDeclarations
// declaration-graph.mts#collectFrom
// declaration-graph.mts#collectInstances
// declaration-graph.mts#collect
// declaration-graph.mts#elaborateDeclaration
type Hook = (
  n: number,
  read: (n: number) => Within<{ value: "any"; store: "grow" }, string>,
) => Within<{ value: "any"; store: "grow" }, string>;
export function invoke(hook: Hook, ...args: Parameters<Hook>): string {
  return hook(...args);
}
