import { at } from "@fixture/closure-bounded";
export function first(xs: number[]): number {
  return xs.length > 0 ? at(xs, 0) : 0;
}
