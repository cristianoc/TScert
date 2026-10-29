// `userInfo({ encoding: "buffer" })` encodes the user's entry as `Buffer`s
// (run under Node: `typeof` of its `homedir` is "object"). The entry states
// `userInfo` at no argument alone: refused.
import { userInfo } from "node:os";

export function home(): string {
  return typeof userInfo({ encoding: "buffer" }).homedir;
}
