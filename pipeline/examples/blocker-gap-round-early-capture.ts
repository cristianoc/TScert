// Early use of capturedAt; outer arrow has no result annotation.
// Census functions:
// declaration-graph.mts#collectDeclarations
export function use(): number {
  const earlier = (): number => capturedAt(1)(2);
  const capturedAt =
    (use: number) =>
    (parameter: number): number =>
      use + parameter;
  return earlier();
}
