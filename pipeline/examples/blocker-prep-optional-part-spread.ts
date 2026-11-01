// Census functions:
// fragment-parts.mts#mapExprParts
// fragment-parts.mts#deepPartMap
// fragment-parts.mts#directParts
// fragment-parts.mts#forEachPart
// fragment-parts.mts#fragmentTypes
// fragment-parts.mts#moduleHolds
// fragment-parts.mts#astHolds
type Part = { spread: number } | { name: string; e: number; spread?: never };
export function parts(
  ps: Part[],
  map: (x: number) => Within<{ value: "any"; store: "grow" }, number>,
): Part[] {
  return ps.map((p): Part => {
    if (p.spread !== undefined) return { ...p, spread: map(p.spread) };
    return { ...p, e: map(p.e) };
  });
}
