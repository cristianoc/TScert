// The callback-free node methods change no location of the model, on a
// throw too (T3, COMPILER-API.md, "Node methods and callbacks"): `map`
// callbacks calling `getStart`, `getText`, `getSourceFile` and a file's
// `getLineAndCharacterOfPosition` are within the empty footprint, so each
// result is dense, and a `findIndex` callback calling `getEnd` passes each
// visit an element.
import type { Node } from "typescript/unstable/ast";

export function starts(nodes: Node[]): number[] {
  const r: number[] = nodes.map((n) => n.getStart());
  return r;
}

export function texts(nodes: Node[]): string[] {
  const r: string[] = nodes.map((n) => n.getText());
  return r;
}

export function lines(nodes: Node[]): number[] {
  const r: number[] = nodes.map(
    (n) => n.getSourceFile().getLineAndCharacterOfPosition(n.getStart()).line,
  );
  return r;
}

export function firstEndingAt(nodes: Node[], end: number): number {
  return nodes.findIndex((n) => n.getEnd() === end);
}
