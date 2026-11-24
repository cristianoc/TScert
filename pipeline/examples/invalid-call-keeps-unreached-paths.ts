// A call whose frame reaches a narrowed path ends it: `flip` changes the
// `k` field of the object it is passed, so after `flip(d.tag)` the field
// holds `"pat"`, outside the declared result (run under Node:
// `f({ tag: { k: "id" } })` returns "pat").
type Tag = { k: "id" | "pat" };
type Decl = { tag: Tag };
function flip(n: Tag): Modifies<{ "n.k": "scalar" }, void> {
  n.k = "pat";
}
export function f(d: Decl): "id" | "none" {
  if (d.tag.k !== "id") return "none";
  flip(d.tag);
  return d.tag.k;
}
