// A negated guard call as the left operand of `||` or `&&` is a dispatch on
// the call itself: on the arm where the call answered `true`, the right
// operand, a closure it creates and the statement after the condition read
// the guarded name at the promised type. Two operands negated, three
// operands regrouped, and a guard whose evaluation has effects, run once
// and in order.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type Fields = { [key: string]: Json };
function isRecord(v: Json | undefined): v is Fields {
  if (typeof v !== "object" || v === null || Array.isArray(v)) return false;
  return true;
}
export function bounded(v: Json | undefined, n: number): Fields {
  if (!isRecord(v) || n > 3) throw Error("invalid");
  return v;
}
export function keyed(v: Json | undefined, required: string[]): Fields {
  if (!isRecord(v) || required.some((k) => !(k in v))) throw Error("invalid");
  return v;
}
export function exact(
  v: Json | undefined,
  required: string[],
  optional: string[],
): Fields {
  if (
    !isRecord(v) ||
    required.some((k) => !(k in v)) ||
    Object.keys(v).some((k) => ![...required, ...optional].includes(k))
  )
    throw Error("invalid");
  return v;
}
export function both(v: Json | undefined, w: Json | undefined): Fields[] {
  if (!isRecord(v) || !isRecord(w)) throw Error("invalid");
  return [v, w];
}
export function neither(v: Json | undefined, n: number): number {
  if (!isRecord(v) && n > 3) return 0;
  return 1;
}
function tick(log: string[], v: Json | undefined): boolean {
  log.push("a");
  return isRecord(v);
}
function tock(log: string[]): boolean {
  log.push("b");
  return true;
}
export function ordered(log: string[], v: Json | undefined): string[] {
  if (!tick(log, v) || tock(log)) log.push("c");
  return log;
}
