// A catch returning normally observes arbitrary changes made before a throw.
export function wrong(
  xs: number[],
): Modifies<{ values: "any"; stores: "grow" }, number> {
  try {
    xs.pop();
    throw 0;
  } catch {
    return 0;
  }
}
