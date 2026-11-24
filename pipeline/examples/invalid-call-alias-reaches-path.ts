// A call through an alias reaches a narrowed path: `flip(t)` changes the
// `k` field of `t`, which may be `d.tag` (run under Node:
// `(() => { const d = { tag: { k: "id" } }; return f(d, d.tag); })()`
// returns "pat").
type Tag = { k: "id" | "pat" };
type Decl = { tag: Tag };
function flip(n: Tag): Modifies<{ "n.k": "scalar" }, void> {
  n.k = "pat";
}
export function f(d: Decl, t: Tag): "id" | "none" {
  if (d.tag.k !== "id") return "none";
  flip(t);
  return d.tag.k;
}
