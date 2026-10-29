// `tmpdir`, which program modules re-export from `node:os` by name and by
// `export *`: each binding is `node:os`'s own export, read at its reviewed
// entry, a string.
import { tmpdir } from "@fixture/node-os-named";
import { tmpdir as starred } from "@fixture/node-os-star";
export function both(): string {
  return tmpdir() + starred();
}
