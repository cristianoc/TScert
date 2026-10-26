// Options holding a getter: the host reads `bigint` and `throwIfNoEntry`
// inside the call (run under Node: the getter runs during the call, once).
// An accessor is outside the source fragment, and the reviewed entry admits
// no options: refused at the getter.
import { statSync } from "node:fs";

let reads: number = 0;
const options = {
  get bigint(): false {
    reads++;
    return false;
  },
};
export function size(path: string): number {
  return statSync(path, options).size + reads;
}
