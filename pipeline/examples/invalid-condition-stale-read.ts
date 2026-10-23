// A write between the read of a field and its comparison: the comparison is
// of the value read before the write. Run under Node: `staleRead` answers
// `true` of a box it leaves at "intersection".
type Box = { k: "union" | "intersection" };

export function staleRead(b: Box): b is { k: "union" } {
  return b.k === (b.k = "intersection", "union");
}
