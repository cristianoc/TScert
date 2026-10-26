// A getter for `update` on `Hash.prototype` runs at the method's lookup,
// before the call (run under Node: it pops the array).
import { createHash } from "node:crypto";

export function hook(xs: number[]): void {
  Object.defineProperty(Object.getPrototypeOf(createHash("sha256")), "update", {
    get() {
      xs.pop();
      return () => undefined;
    },
  });
}
