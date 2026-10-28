// A function a record field holds, passed to map, needs its effect stated:
// a field's function type states none, so map takes it at any footprint.
// Census functions:
// fragment-parse.mts#renamedModule, fragment-parts.mts#astHolds,
// fragment-parts.mts#codeParts, fragment-parts.mts#deepPartMap,
// fragment-parts.mts#directParts, fragment-parts.mts#documentHolds,
// fragment-parts.mts#documentParts, fragment-parts.mts#forEachPart,
// fragment-parts.mts#fragmentTypes, fragment-parts.mts#mapDocument,
// fragment-parts.mts#mapExprParts, fragment-parts.mts#mapFunctionParts,
// fragment-parts.mts#mapStmtParts, fragment-parts.mts#moduleHolds.
interface Mapper {
  expr: (e: number) => number;
}
export function all(list: readonly number[], m: Mapper): number[] {
  return list.map(m.expr);
}
