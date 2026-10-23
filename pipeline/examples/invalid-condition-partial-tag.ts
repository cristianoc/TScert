// A tag test whose answer covers the arm's tag set in part: `"union"` is
// not `"intersection"`. Run under Node.
type Box = { k: "union" | "intersection" };

export function partialTag(b: Box): b is { k: "intersection" } {
  return b.k === "union";
}
