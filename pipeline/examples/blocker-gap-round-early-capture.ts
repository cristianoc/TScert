// An early binding states the function its outer arrow returns.
// Census functions:
// declaration-graph.mts#collectDeclarations
export function use(): number {
  const earlier = (): number => capturedAt(1)(2);
  const capturedAt =
    (use: number): ((parameter: number) => number) =>
    (parameter: number): number =>
      use + parameter;
  return earlier();
}
