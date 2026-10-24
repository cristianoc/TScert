// `forEachChild` with both visitors, each within a closed footprint, is
// within the larger (COMPILER-API.md, "Node methods and callbacks"); a call
// passing a list visitor has no derivation of its node typing, at any
// footprint, outside a callback too.
import type { Node } from "typescript/unstable/ast";

export function visits(n: Node): number {
  let k = 0;
  n.forEachChild(
    () => {
      k++;
    },
    () => {
      k++;
    },
  );
  return k;
}

export function mixed(nodes: Node[]): number[] {
  const r: number[] = nodes.map((n) => {
    const lists: number[] = [];
    const found = n.forEachChild(
      (c) => (c.getEnd() > 3 ? c.getEnd() : undefined),
      () => {
        lists.push(1);
        return undefined;
      },
    );
    return (found ?? 0) + lists.length;
  });
  return r;
}
