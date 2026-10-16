// An imported guard's promise is checked by its own module's run, which this
// one's does not see: the import is read at its declared function type,
// which states no promise.
import { isWord } from "@fixture/lib";

export function size(v: unknown): number {
  return isWord(v) ? v.length : 0;
}
