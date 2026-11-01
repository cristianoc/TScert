// Census functions:
// declaration-graph.mts#declarationAnswer
// declaration-graph.mts#declarationServices
// declaration-graph.mts#collectDeclarations
export function call(fn: (x: string) => string, x: string): string {
  return Reflect.apply(fn, undefined, [x]);
}
