// An importer reading the promise of a guard its module's check refuses:
// `isText` returns `true` for a number, so no interface entry states its
// promise and the import is read at the ordinary effect, narrowing nothing;
// the read `x.length` is refused. Under Node `size(3)` returns `undefined`,
// not a number.
import { isText } from "@fixture/guards";

export function size(x: string | number): number {
  return isText(x) ? x.length : 0;
}
