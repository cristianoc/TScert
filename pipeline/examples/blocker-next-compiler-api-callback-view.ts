// Census: tools/written-applications.mts#pairOf.
import * as ts from "typescript/unstable/ast";
export function matching(
  owner: ts.ObjectLiteralExpression,
  d: ts.Node,
  name: string,
): ts.Node[] {
  const properties: readonly ts.Node[] = owner.properties;
  return properties.filter(
    (m) =>
      m !== d &&
      (ts.isGetAccessorDeclaration(m) || ts.isSetAccessorDeclaration(m)) &&
      m.name.getText(m.getSourceFile()) === name,
  );
}
