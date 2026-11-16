// A footprint promised on throws also covers every rethrowing handler.
export function wrong(
  xs: number[],
  query: () => Modifies<{ values: "any"; spines: "grow" }, number>,
): Modifies<{ values: "any"; spines: "grow"; onThrow: true }, number> {
  try {
    return query();
  } catch (error) {
    xs.pop();
    throw error;
  }
}
