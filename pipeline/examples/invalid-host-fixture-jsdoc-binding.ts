// A binding pattern reads `jsDoc`, which the host type's shape omits:
// refused.
import type { Node } from "@fixture/host";

export function docs(n: Node): unknown {
  const { jsDoc } = n;
  return jsDoc;
}
