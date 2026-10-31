// Census: declaration-graph.mts#collectDeclarations.
// Reading an optional field of a parameter whose default is an empty object.
export function config(
  options: { tsconfigPath?: string } = {},
): string | undefined {
  return options.tsconfigPath;
}
