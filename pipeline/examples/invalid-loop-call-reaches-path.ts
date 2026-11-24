// A loop whose body calls `flip` ends the narrowing `flip`'s frame reaches:
// `ts` may hold `d.tag` (run under Node:
// `(() => { const d = { tag: { k: "id" } }; return f(d, [d.tag]); })()`
// returns "pat").
type Tag = { k: "id" | "pat" };
type Decl = { tag: Tag };
function flip(n: Tag): Modifies<{ "n.k": "scalar" }, void> {
  n.k = "pat";
}
export function f(d: Decl, ts: Tag[]): "id" | "none" {
  if (d.tag.k !== "id") return "none";
  for (const t of ts) flip(t);
  return d.tag.k;
}
