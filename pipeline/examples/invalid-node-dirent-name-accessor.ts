// An accessor on `Dirent.prototype` turns the constructor's write of `name`
// into a call.
import { Dirent } from "node:fs";

export function hide(): void {
  Object.defineProperty(Dirent.prototype, "name", {
    set() {},
    get() {
      return 7;
    },
  });
}
