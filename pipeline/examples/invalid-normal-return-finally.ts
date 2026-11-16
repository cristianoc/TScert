// A finalizer's return overrides the throw and exposes the changed store.
export function wrong(
  xs: number[],
): Modifies<{ values: "any"; spines: "grow" }, number> {
  try {
    xs.pop();
    throw 0;
  } finally {
    return 0;
  }
}
