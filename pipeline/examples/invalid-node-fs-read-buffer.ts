// `readFileSync` without an encoding returns a `Buffer`, a form the reviewed
// overlay does not state: the call is outside the stated one.
import { readFileSync } from "node:fs";

export function size(file: string): number {
  return readFileSync(file).length;
}
