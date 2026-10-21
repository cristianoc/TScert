// A guard read as a value and passed to `filter`: TypeScript resolves the
// guard overload and types the result at the promise's type, while the
// guard's promise signature takes one parameter of the callback's three and
// meets only the plain overload, so the result keeps the element type. The
// closure over the result, which TypeScript types at the promise's type, is
// claimed at the element type and refused at its parameter.
type Declaration = { kind: "declaration"; body: boolean };
type Other = { kind: "other" };

function isDeclaration(d: Declaration | Other): d is Declaration {
  return d.kind === "declaration";
}

export function defined(statements: (Declaration | Other)[]): boolean {
  return statements.filter(isDeclaration).some((d) => d.body);
}
