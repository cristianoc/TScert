// `availableParallelism()` and `userInfo()` from `node:os`, read through
// their reviewed entries: a number within the empty footprint, and a fresh
// record of the user's entry whose fields are writable.
import { availableParallelism, userInfo } from "node:os";

export function parts(): number {
  return Math.max(1, Math.min(8, availableParallelism() - 1));
}

export function home(): string {
  const info = userInfo();
  info.homedir = info.homedir + "/";
  return info.shell === null ? info.homedir : `${info.homedir}${info.username}${info.uid + info.gid}`;
}
