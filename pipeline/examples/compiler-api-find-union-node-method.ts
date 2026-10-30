// `find` callbacks calling a node method on a value of several node kinds:
// `selectGlobal`'s and `globalFunction`'s overload search
// (tools/declaration-graph.mts), `makeProbe`'s copied part
// (tools/type-probe.mts) and `lowerFile`'s root declaration
// (tools/fragment-parse.mts). Each kind holds the method, which the
// audited contract states changes no array store, so the member is bound
// to the object and called at that effect: the callback keeps every array
// store, and each visit passes an element.
import * as ts from "typescript/unstable/ast";

export function overloadAt(
  overloads: readonly ts.FunctionDeclaration[],
  resolved: ts.Node | undefined,
): ts.FunctionDeclaration | undefined {
  return overloads.find(
    (o) =>
      resolved &&
      o.pos === resolved.pos &&
      o.end === resolved.end &&
      o.getSourceFile().fileName === resolved.getSourceFile().fileName,
  );
}

export function copiedAt(
  copied: ts.Node[],
  file: string,
  start: number,
): ts.Node | undefined {
  return copied.find(
    (n) =>
      n.getSourceFile().fileName === file &&
      n.getStart(n.getSourceFile()) === start,
  );
}

export function rootAt(
  imports: ts.ImportDeclaration[],
  locals: (ts.InterfaceDeclaration | ts.ClassDeclaration)[],
  globals: ts.Identifier[],
  source: ts.SourceFile,
  start: number,
): ts.Node | undefined {
  return [...imports, ...locals, ...globals].find(
    (n) => n.getStart(source) === start,
  );
}

// A token of a generic token family, an intersection holding the method
// through its base.
export function beside(
  nodes: readonly ts.FunctionDeclaration[],
  token: ts.Identifier | ts.Token<ts.SyntaxKind.CommaToken>,
): ts.FunctionDeclaration | undefined {
  return nodes.find((n) => n.getSourceFile() === token.getSourceFile());
}
