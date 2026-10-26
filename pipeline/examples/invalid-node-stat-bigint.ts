// `bigint: true` gives a `BigIntStats`, whose numbers are bigints (run under
// Node: `typeof size` is "bigint"): the reviewed entry admits no options,
// refused.
import { statSync } from "node:fs";

export function size(path: string): bigint {
  return statSync(path, { bigint: true }).size;
}
