// The array invariant excludes an own Symbol.iterator. Replacing it runs
// arbitrary code during rest collection and can violate the growth promise.
export function changed(
  xs: number[],
  victim: number[],
): Within<{ value: "any"; store: "grow" }, number> {
  const alias: { [Symbol.iterator]: () => Iterator<number> } = xs;
  alias[Symbol.iterator] = (): Iterator<number> => {
    victim.pop();
    return [1].values();
  };
  const [...tail] = xs;
  return tail.length;
}
