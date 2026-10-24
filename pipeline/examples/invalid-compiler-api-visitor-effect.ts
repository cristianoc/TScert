// `forEachChild` runs its visitor, and its call is within the visitor's
// footprint: a visitor popping the mapped array is within no footprint that
// keeps array stores, so a `map` callback calling it is unrestricted, and the
// result may hold holes (run under Node: a hole).
import type { Node } from "typescript/unstable/ast";

export function wrong(nodes: Node[]): number[] {
  const r: number[] = nodes.map((n) => {
    n.forEachChild(() => {
      nodes.pop();
    });
    return 0;
  });
  return r;
}
