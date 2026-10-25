export function effects(
  cell: { value: number },
  flag: boolean,
): Within<{ value: "keep"; store: "keep" }, number> {
  const bad = flag as number;
  cell.value = 1;
  return bad;
}
