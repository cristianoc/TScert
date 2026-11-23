// The walker of review2.ts, imported through a re-export and held by a
// constant, through which a call's instance is not checked.
import { walkRe } from "./review2-reexporter.js";

export function truncate(xs: number[]): number {
  const f = walkRe;
  return f(xs, () => {
    xs.length = 0;
  });
}
