// A namespace consumed whole: its exported members' annotations are swept,
// and `B<any>` there keeps its bound.
type V = typeof import("@fixture/whole").Space extends { m: "a" }
  ? "yes"
  : "no";
export function f(x: V): "yes" {
  return x;
}
