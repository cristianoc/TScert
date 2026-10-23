// The false outcome of `||` past a call in its right operand: the field the
// left operand found "union" may hold anything its contract admits. Run
// under Node: `staleOr` returns "intersection".
type Box = { k: "union" | "intersection" };

export function staleOr(b: Box, f: () => boolean): "union" {
  if (b.k !== "union" || f()) return "union";
  return b.k;
}
