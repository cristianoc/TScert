// `fileURLToPath`'s options select Windows paths (run under Node:
// `file:///C:/x` gives `C:\x`): the entry states one argument, refused.
import { fileURLToPath } from "node:url";

export function windowsPath(url: string): string {
  return fileURLToPath(url, { windows: true });
}
