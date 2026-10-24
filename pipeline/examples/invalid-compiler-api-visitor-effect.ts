// `forEachChild` runs its visitor, whose effect is the caller's: its
// declared signature states none, so a `map` callback calling it with a
// visitor popping the mapped array is unrestricted, and the result may hold
// holes (run under Node: a hole).
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
