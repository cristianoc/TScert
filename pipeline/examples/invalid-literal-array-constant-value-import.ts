// An imported constant initialized by `[1, 2]` is a writable `number[]`, the
// type TypeScript infers, not an array of its literals: any number may be
// written into it, and an element is not returned at `1 | 2`.
import { offsets } from "@fixture/lib";

export function one(): 1 | 2 {
  return offsets[0] ?? 1;
}
