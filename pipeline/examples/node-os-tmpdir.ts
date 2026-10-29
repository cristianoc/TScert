// `tmpdir()` from `node:os`, read through its reviewed entry: a string.
import { tmpdir } from "node:os";
import { join } from "node:path";

export function scratch(name: string): string {
  return join(tmpdir(), name);
}
