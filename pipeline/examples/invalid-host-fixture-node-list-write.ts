// A node list's own members are readonly views: a write to its declared
// writable `transformFlags` is refused (R1).
import type { Block } from "@fixture/host";

export function mark(b: Block): void {
  b.statements.transformFlags = 1;
}
