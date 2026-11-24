// An argument is typed at its parameter's type, as an annotated binding's
// initializer is: `new Map()` passed at `Map<string, number>` takes that
// instance, and `new Set()` at `Set<string>` likewise.
// Census functions:
// claim-text.mts#lift, fragment-statements.mts#forOfPattern.
function total(t: Map<string, number>, d: number): number {
  return t.size + d;
}
function count(s: Set<string>, extra: string[]): number {
  for (const x of extra) s.add(x);
  return s.size;
}
export function outer(d: number, xs: string[]): number {
  return total(new Map(), d) + count(new Set(), xs);
}
