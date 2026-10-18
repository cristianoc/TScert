// `realpathSync` is read at one argument: an encoding option, which may
// select a Buffer result (`"buffer"`), is outside the stated call.
import { realpathSync } from "node:fs";

export function real(root: string): string {
  return realpathSync(root, "utf8");
}
