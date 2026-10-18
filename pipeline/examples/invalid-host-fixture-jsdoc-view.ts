// A node assigned to a structural type stating `jsDoc`: the host type's
// shape states no `jsDoc`, so no such type admits a node, and the view's
// read never happens.
import type { Node } from "@fixture/host";

export function docs(n: Node): unknown {
  const view: { readonly jsDoc?: readonly Node[] | undefined } = n;
  return view.jsDoc;
}
