// A plain tuple carries no marker: it is not a `Managed` tuple.
import type { Managed } from "@fixture/lib";
function first(xs: [number, number] & Managed): number {
  return xs[0];
}
export function plain(xs: [number, number]): number {
  return first(xs);
}
