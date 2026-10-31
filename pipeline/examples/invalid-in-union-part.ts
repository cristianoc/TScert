// The original part contract admits an unstated spread of any type,
// including a getter, on its named arm.
type Part = { name: string; e: number } | { spread: number };
export function partValue(p: Part): unknown {
  return "spread" in p ? p.spread : p.e;
}
