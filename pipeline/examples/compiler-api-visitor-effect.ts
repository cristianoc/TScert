// `forEachChild` runs no client code but its visitors and its own steps
// change no location of the model (T3, COMPILER-API.md, "Node methods and
// callbacks"): with its visitor within a closed footprint its call is within
// it, so `map` callbacks calling it with a visitor keeping every array
// store, or growing an array the callback allocated, give dense results.
import type { Node } from "typescript/unstable/ast";

export function firstChildTexts(nodes: Node[]): string[] {
  const r: string[] = nodes.map(
    (n) =>
      n.forEachChild((c) => (c.getStart() > 0 ? c.getText() : undefined)) ?? "",
  );
  return r;
}

export function childCounts(nodes: Node[]): number[] {
  const r: number[] = nodes.map((n) => {
    const seen: Node[] = [];
    n.forEachChild((c) => {
      seen.push(c);
    });
    return seen.length;
  });
  return r;
}
