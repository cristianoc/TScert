// A look-alike the program declares has no marker: its type is an ordinary
// record, and a test of its `kind` narrows the union the program wrote by the
// ordinary rules (HOST-FAMILIES.md, "Activation"). A compiler-API node is one
// of its values where the record states only members every node has.
import * as ts from "typescript/unstable/ast";

interface Named {
  readonly kind: 1;
  readonly text: string;
}
interface Other {
  readonly kind: 2;
}

export function text(n: Named | Other): string {
  return n.kind === 1 ? n.text : "";
}

export function width(n: ts.Node): number {
  const range: { readonly pos: number; readonly end: number } = n;
  return range.end - range.pos;
}
