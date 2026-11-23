// The walker of review2.ts, imported from another directory and held by a
// constant, through which a call's instance is not checked.
import { walkFar } from "../review2.js";

export function truncate(xs: number[]): number {
  const f = walkFar;
  return f(xs, () => {
    xs.length = 0;
  });
}
