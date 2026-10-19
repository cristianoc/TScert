// An ancestor inserted above `Dirent.prototype`, with an accessor `name`,
// turns the constructor's assignment into a call though both Node
// prototypes still hold data properties only (run under Node: the name is
// 7 and not own).
import { Dirent } from "node:fs";

export function insert(ancestor: object): void {
  Object.setPrototypeOf(Dirent.prototype, ancestor);
}
