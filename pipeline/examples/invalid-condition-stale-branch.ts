// A statement's branch past a call in the condition's right operand: the
// field the left operand tested may hold anything its contract admits.
// Run under Node: `staleIf` returns "intersection".
type Box = { k: "union" | "intersection" };

export function staleIf(b: Box, f: () => void): "union" {
  if (b.k === "union" && (f(), true)) return b.k;
  return "union";
}
