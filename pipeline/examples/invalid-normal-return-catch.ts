// A catch returning normally observes arbitrary changes made before a throw.
export function wrong(
  xs: number[],
): Within<{ value: "any"; store: "grow" }, number> {
  try {
    xs.pop();
    throw 0;
  } catch {
    return 0;
  }
}
