// A class consumed whole: every member's type is determined by its
// annotations, and an inferred member's is refused.
type V = import("@fixture/whole").Inferred extends { m: "a" } ? "yes" : "no";
export function f(x: V): "yes" {
  return x;
}
