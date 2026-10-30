// Grouped switch cases meet at one clause: the case of an arm whose field
// type is the case's literal enters it with no observed fact of the field,
// and the arm's field type states it.
type Shape =
  | { k: "a"; x: number }
  | { k: "b" | "c"; y: string }
  | { k: "d"; z: boolean };

export function grouped(s: Shape): "a" | "b" | "d" | "c" {
  switch (s.k) {
    case "c":
      return "c";
    case "a":
    case "b":
    case "d":
      return s.k;
  }
}
