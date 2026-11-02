// Census: tools/declaration-graph.mts#settleDeclarations.
export function replace(a: number[], b: number[]): void {
  a.splice(0, a.length, ...b);
}
