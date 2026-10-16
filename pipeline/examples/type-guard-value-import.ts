// An imported guard narrows at its call by the promise its declared type
// states, which its own module's run checks at its body.
import { isWord } from "@fixture/lib";

export function size(v: unknown): number {
  return isWord(v) ? v.length : 0;
}
