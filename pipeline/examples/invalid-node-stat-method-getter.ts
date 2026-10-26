// A getter for `isFile` on `Stats.prototype` runs where the member is read,
// a read no call's effect covers (run under Node: a `map` callback reading
// `s.isFile` pops the mapped array and leaves a hole).
import { Stats, statSync } from "node:fs";

export function hook(xs: number[]): void {
  const original = Stats.prototype.isFile;
  Object.defineProperty(Stats.prototype, "isFile", {
    get() {
      xs.pop();
      return original;
    },
  });
}
export function rows(xs: number[], path: string): number[] {
  const s = statSync(path);
  return xs.map(() => {
    const f = s.isFile;
    return f === undefined ? 0 : 1;
  });
}
