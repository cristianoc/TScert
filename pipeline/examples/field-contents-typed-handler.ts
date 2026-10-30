// A handler recovers the field contract from its unrefined source context.
// Diagnostic traversal checks the same typed-cell facts as acceptance.
type Shape =
  | { k: "a"; x: number }
  | { k: "b" | "c"; y: string }
  | { k: "d"; z: boolean };

export function grouped(s: Shape, mayThrow: () => void): "a" | "b" | "c" | "d" {
  try {
    mayThrow();
  } catch {
    switch (s.k) {
      case "c":
        return "c";
      case "a":
      case "b":
      case "d":
        return s.k;
    }
  }
  return "a";
}
