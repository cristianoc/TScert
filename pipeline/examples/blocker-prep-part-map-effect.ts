// Census functions:
// fragment-parts.mts#partsOf
// fragment-parts.mts#codeParts
type Mapper = {
  expr: (
    e: number,
    ...further: unknown[]
  ) => Within<{ value: "any"; store: "grow" }, number>;
};
export function partsOf(
  map: (m: Mapper) => unknown,
): Within<{ value: "any"; store: "grow" }, number[]> {
  const parts: number[] = [];
  map({
    expr: (e) => {
      parts.push(e);
      return e;
    },
  });
  return parts;
}
