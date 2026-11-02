// Census function: declaration-graph.mts#promisedDefinitions.
interface Definition {
  module: string;
  expression: { value: number } | null;
}
export function promised(
  definitions: readonly Definition[],
  client: string,
): Definition[] {
  const local: Set<string> = new Set(["local"]);
  return definitions.map((d) =>
    d.module === client || local.has(d.module)
      ? d
      : { ...d, expression: d.expression && { value: d.expression.value } },
  );
}
