// A getter for `isDirectory` on `Dirent.prototype` runs at the method's
// lookup, before the call whose effect is stated (run under Node: it pops
// the array).
import { Dirent } from "node:fs";

export function hook(xs: number[]): void {
  Object.defineProperty(Dirent.prototype, "isDirectory", {
    get() {
      xs.pop();
      return () => true;
    },
  });
}
