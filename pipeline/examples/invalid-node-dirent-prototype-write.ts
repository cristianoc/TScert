// A write to `Dirent.prototype` replaces a member every entry reads.
import { Dirent } from "node:fs";

export function replace(): void {
  Dirent.prototype.isDirectory = () => true;
}
