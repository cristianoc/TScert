// An outer catch can turn an inner rethrow into a normal return.
export function wrong(
  xs: number[],
  query: () => Modifies<{ values: "any"; spines: "grow" }, number>,
): Modifies<{ values: "any"; spines: "grow" }, number> {
  try {
    try {
      return query();
    } catch (error) {
      xs.pop();
      throw error;
    }
  } catch {
    return 0;
  }
}
