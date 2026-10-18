// A node list read as a dense readonly array of its elements
// (COMPILER-API.md, "Node lists"): its length, iteration, spread, the
// readonly array members, `at`, and as a `readonly Node[]` argument.
import type { Block, Node } from "@fixture/host";

function size(nodes: readonly Node[]): number {
  return nodes.length;
}

export function rows(b: Block): number {
  const list = b.statements;
  let total = 0;
  for (const s of list) total = total + s.kind;
  const kinds = list.map((s) => s.kind);
  const first = list.at(0);
  const copy = [...list];
  return (
    total +
    kinds.length +
    (list.some((s) => s.kind === 1) ? 1 : 0) +
    (first === undefined ? 0 : first.kind) +
    size(list) +
    copy.length
  );
}
