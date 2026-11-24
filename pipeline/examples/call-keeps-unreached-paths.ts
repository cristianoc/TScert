// A call keeps the narrowed member paths its normal exit's frame leaves
// unchanged: `m.set` changes only `m.size`, `bump` only `b.n`, so `d.name`
// stays at its `"id"` arm across both, and across a loop whose body calls
// `slots.add`.
// Census functions:
// fragment-statements.mts#forInStmt, diagnostic-view.mts#presentObligation.
type Name = { k: "id"; text: string } | { k: "pat"; parts: string[] };
type Decl = { name: Name };
type Box = { n: number };
function bump(o: Box): Modifies<{ "o.n": "scalar" }, void> {
  o.n = o.n + 1;
}
function local(n: { k: "id"; text: string }): string {
  return n.text;
}
export function named(d: Decl, r: number, b: Box): string {
  if (d.name.k !== "id") return "";
  const m = new Map<number, string>();
  m.set(r, "x");
  bump(b);
  return local(d.name);
}
export function counted(d: Decl, xs: number[]): string {
  const slots = new Set<number>();
  if (d.name.k !== "id") return "";
  for (const x of xs) slots.add(x);
  return local(d.name);
}
