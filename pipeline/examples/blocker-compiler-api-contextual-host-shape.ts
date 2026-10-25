// A filter callback over object-literal members needs its contextual host
// shape covered by the offered signature.
// Census functions:
// written-applications.mts#pairOf.
import * as ts from "typescript/unstable/ast";
export function use(d: ts.Node): ts.Node[] {
  const owner = d.parent;
  if (
    !(ts.isGetAccessorDeclaration(d) || ts.isSetAccessorDeclaration(d)) ||
    !owner ||
    !ts.isObjectLiteralExpression(owner)
  )
    return [];
  const name = d.name.getText(d.getSourceFile());
  return owner.properties.filter(
    (m) =>
      m !== d &&
      (ts.isGetAccessorDeclaration(m) || ts.isSetAccessorDeclaration(m)) &&
      m.name.getText(m.getSourceFile()) === name,
  );
}
