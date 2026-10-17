// A computed read whose key is a constant holding "jsDoc": refused, as the
// member is no member of the host type's shape.
import type { Node } from "@fixture/host";

export function docs(n: Node): unknown {
  const key = "jsDoc";
  return n[key];
}
