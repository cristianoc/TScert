// A read of `jsDoc`, which the host type's shape omits: refused.
import type { Node } from "@fixture/host";

export function docs(n: Node): unknown {
  return n.jsDoc;
}
