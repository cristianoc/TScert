// A test replaced by a value no call accepts, or deleted, leaves an entry's
// `isDirectory` no function (run under Node: a number, then `undefined`).
import { Dirent } from "node:fs";

export function replace(): void {
  Reflect.set(Dirent.prototype, "isDirectory", 7);
}
export function remove(): void {
  Reflect.deleteProperty(Dirent.prototype, "isDirectory");
}
