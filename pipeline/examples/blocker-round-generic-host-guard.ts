// A generic host guard followed by getStart and an end read.
// Census functions:
// type-probe.mts#nodeAt
// type-probe.mts#makeProbe
import type { Node, SourceFile } from "typescript/unstable/ast";
export function nodeAt<N extends Node>(
  file: SourceFile,
  start: number,
  end: number,
  test: (n: Node) => n is N,
): N | undefined {
  let found: N | undefined;
  const visit = (n: Node): void => {
    if (found || n.end < start || n.pos > end) return;
    if (test(n) && n.getStart(file) === start && n.end === end) found = n;
    else n.forEachChild(visit);
  };
  visit(file);
  return found;
}
