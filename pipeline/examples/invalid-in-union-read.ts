// Census: fragment-parts.mts#mapExprParts and its callers deepPartMap,
// directParts, forEachPart, fragmentTypes, moduleHolds and astHolds.
// A named part states the absence of a spread value, as ObjectPart does.
type Part = { name: string; e: number; spread?: never } | { spread: number };
export function partValue(p: Part): number {
  return p.spread !== undefined ? p.spread : p.e;
}
