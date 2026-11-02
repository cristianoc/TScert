// A footprint promised on throws also covers every rethrowing handler.
export function wrong(
  xs: number[],
  query: () => Within<{ value: "any"; store: "grow" }, number>,
): Within<{ value: "any"; store: "grow"; onThrow: true }, number> {
  try {
    return query();
  } catch (error) {
    xs.pop();
    throw error;
  }
}
