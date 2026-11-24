// A narrowed path across `x.toString()` on `string | number`: the lowered
// call's object arm calls a member no contract states, of the ordinary
// effect, which ends `d.name`'s narrowing, though no value reaches that arm.
type Name = { k: "id"; text: string } | { k: "pat"; parts: string[] };
type Decl = { name: Name };
function local(n: { k: "id"; text: string }): string {
  return n.text;
}
export function shown(d: Decl, x: string | number): string {
  if (d.name.k !== "id") return "";
  const s = x.toString();
  return local(d.name) + s;
}
