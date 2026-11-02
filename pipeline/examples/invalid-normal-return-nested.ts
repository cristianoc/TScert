// An outer catch can turn an inner rethrow into a normal return.
export function wrong(
  xs: number[],
  query: () => Within<{ value: "any"; store: "grow" }, number>,
): Within<{ value: "any"; store: "grow" }, number> {
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
