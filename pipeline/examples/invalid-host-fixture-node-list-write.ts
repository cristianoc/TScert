// A node list's own members are not read: a write to its declared writable
// `transformFlags` is refused (R1, L2).
import type { Block } from "@fixture/host";

export function mark(b: Block): void {
  b.statements.transformFlags = 1;
}
