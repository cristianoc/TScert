// Census functions:
// fragment-parts.mts#partsOf
// fragment-parts.mts#codeParts
type Mapper = {
  expr: (
    e: number,
    ...further: unknown[]
  ) => Modifies<{ values: "any"; spines: "grow" }, number>;
};
export function partsOf(
  map: (m: Mapper) => Modifies<{ values: "any"; spines: "grow" }, unknown>,
): Modifies<{ values: "any"; spines: "grow" }, number[]> {
  const parts: number[] = [];
  map({
    expr: (e) => {
      parts.push(e);
      return e;
    },
  });
  return parts;
}
