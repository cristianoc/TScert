// A constant destructured under an annotation: the annotation is swept, and
// `Bounded<any>` there keeps its bound.
export function f(x: keyof { z: typeof import("@fixture/lib").dm }): "z" {
  return x;
}
