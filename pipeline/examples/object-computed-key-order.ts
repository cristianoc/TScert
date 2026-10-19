// A computed key is evaluated, then the value (ECMA-262,
// PropertyDefinitionEvaluation): read before its declaration, the key throws
// before the value runs (run under Node: `log` holds "thrown", then
// "value" once).
export function order(log: string[]): number {
  const make = (): { k: number } => ({ [later]: (log.push("value"), 1) });
  try {
    make();
  } catch {
    log.push("thrown");
  }
  const later: "k" = "k";
  return make().k;
}
