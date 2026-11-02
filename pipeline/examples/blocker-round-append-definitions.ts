// Census function: declaration-graph.mts#appendDocumentDefinitions.
export function append(
  definitions: number[],
  selected: readonly number[],
  stable: boolean,
): void {
  definitions.push(...selected, ...(stable ? [1] : []));
}
