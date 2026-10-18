// A parenthesized literal key reads `jsDoc`: refused.
import type { Node } from "@fixture/host";

export function docs(n: Node): unknown {
  return n["jsDoc"];
}
