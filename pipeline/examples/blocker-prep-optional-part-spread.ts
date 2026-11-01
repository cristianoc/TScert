// Census functions:
// fragment-parts.mts#mapExprParts
// fragment-parts.mts#deepPartMap
// fragment-parts.mts#directParts
// fragment-parts.mts#forEachPart
// fragment-parts.mts#fragmentTypes
// fragment-parts.mts#moduleHolds
// fragment-parts.mts#astHolds
type Part = { spread: number; e?: never } | { e: number; spread?: never };
export function parts(ps: Part[], map: (x: number) => number): Part[] {
  return ps.map((p) =>
    p.spread !== undefined
      ? { ...p, spread: map(p.spread) }
      : { ...p, e: map(p.e) },
  );
}
