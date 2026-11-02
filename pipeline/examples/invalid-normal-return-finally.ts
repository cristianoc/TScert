// A finalizer's return overrides the throw and exposes the changed store.
export function wrong(
  xs: number[],
): Within<{ value: "any"; store: "grow" }, number> {
  try {
    xs.pop();
    throw 0;
  } finally {
    return 0;
  }
}
