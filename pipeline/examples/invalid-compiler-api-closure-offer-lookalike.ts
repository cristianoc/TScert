// A program record with every member `Node` states, its `kind` an
// identifier's, passed to a closure over `Node` through `forEach`: no
// program allocation is a member of the family (HOST-FAMILIES.md,
// "Activation"), so the record is no `Node` and the closure is offered no
// signature at it. The closure's guard reads the look-alike as an
// identifier, whose `text` it lacks: `undefined` goes into the `string[]`.
import * as ts from "typescript/unstable/ast";

interface Lookalike {
  readonly kind: ts.SyntaxKind.Identifier;
  readonly flags: ts.NodeFlags;
  readonly parent: ts.Node;
  readonly pos: number;
  readonly end: number;
  forEachChild<T>(visitor: (node: ts.Node) => T): T | undefined;
  getSourceFile(): ts.SourceFile;
  getStart(): number;
  getFullStart(): number;
  getEnd(): number;
  getWidth(): number;
  getFullWidth(): number;
  getLeadingTriviaWidth(): number;
  getFullText(): string;
  getText(): string;
}

export function wrong(xs: readonly Lookalike[]): string[] {
  const out: string[] = [];
  const one = (e: ts.Node): void => {
    if (ts.isIdentifier(e)) out.push(e.text);
  };
  xs.forEach(one);
  return out;
}
