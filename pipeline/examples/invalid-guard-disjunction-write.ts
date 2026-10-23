// A write between the disjuncts' tests: the right disjunct's call sets the
// tag the left one read. Run under Node: `written` answers `true` of a box
// it leaves at "a".
type Box = { k: "a" | "b" };

export function written(b: Box, g: (b: Box) => void): b is { k: "b" } {
  return b.k === "a" && false || b.k === "b" && (g(b), true);
}
