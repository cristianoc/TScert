// A type-only imported constant as a key: its declaration is swept, and
// `Bounded<any>` there keeps its bound.
import type { k } from "@fixture/lib";
export function f(x: keyof { [k]: number }): "a" {
  return x;
}
