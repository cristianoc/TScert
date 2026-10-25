export function closureEffects(cell: { value: number }): number {
  const run = (): Within<{ value: "keep"; store: "keep" }, number> => {
    cell.value = 1;
    return 1;
  };
  return run();
}
