// `bigint: true` gives a `BigIntStats`, whose numbers are bigints (run under
// Node: `typeof size` is "bigint"): its `size` is refused as a number.
import { statSync } from "node:fs";

export function size(path: string): number {
  // @ts-expect-error: the declaration types `size` as a bigint too.
  return statSync(path, { bigint: true }).size;
}
