// An optional chain reads `jsDoc` where the node is present: refused.
import type { Node } from "@fixture/host";

export function docs(n: Node | undefined): unknown {
  return n?.jsDoc;
}
