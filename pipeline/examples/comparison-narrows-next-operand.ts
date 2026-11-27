// A strict comparison that answered `true` narrows the operands the next
// operand of `||` reads: past `n !== d.name || v !== d.version`, where it
// failed, `n` and `v` are numbers, as the claims at the statement after the
// `if` state (SOURCE-ELABORATION.md, "Contexts").
// Census functions:
// family-activation.mts#checkInventory.
type D = { name: number; version: number };
export function names(n: number | null, v: number | null, d: D): number {
  if (n !== d.name || v !== d.version) return 0;
  return n + v;
}
export function computed(a: number | null, b: number | null, s: number, t: number): number {
  if (a !== s + 0 || b !== t) return 0;
  return a + b;
}
