// Grouped switch cases meet at one clause, where a write through another
// reference may change the tested field: the arm's field type states
// "b" | "c", so after the write the field read is no `"a" | "b"`.
type Shape = { k: "a"; x: number } | { k: "b" | "c"; y: string };

export function grouped(s: Shape, other: { k: "b" | "c"; y: string }): "a" | "b" {
  switch (s.k) {
    case "a":
    case "b":
      other.k = "c";
      return s.k;
    default:
      return "a";
  }
}

