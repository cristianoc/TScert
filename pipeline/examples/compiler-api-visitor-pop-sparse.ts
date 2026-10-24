// A `map` callback calling `forEachChild` with a visitor popping the mapped
// array, at a result type admitting holes: the call is within no footprint
// that keeps array stores, so `map` takes its signature with holes, which
// `(number | undefined)[]` admits.
import type { Node } from "typescript/unstable/ast";

export function shrink(nodes: Node[]): (number | undefined)[] {
  return nodes.map((n) => {
    n.forEachChild(() => {
      nodes.pop();
    });
    return 0;
  });
}
