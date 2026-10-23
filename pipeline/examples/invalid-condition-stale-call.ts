// A call in the right operand of `&&` writes the field the left operand
// tested: past it the field holds what the call wrote. Run under Node:
// `staleCall` answers `true` of a box it leaves at "intersection".
type Box = { k: "union" | "intersection" };

export function staleCall(b: Box): b is { k: "union" } {
  const mutate = (): boolean => {
    b.k = "intersection";
    return true;
  };
  return b.k === "union" && mutate();
}
