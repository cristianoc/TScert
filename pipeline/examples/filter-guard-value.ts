// A guard read as a value and passed to `filter` or `find`: its slot holds
// its promise signature extended by a rest of `unknown` elements, the
// actuals past its parameter it discards, so it meets the guard overload's
// callback, and the result holds the promise's type. A function stating no
// promise meets only the plain overloads, where the result keeps the
// element type.
type Declaration = { kind: "declaration"; body: boolean };
type Other = { kind: "other" };

function isDeclaration(d: Declaration | Other): d is Declaration {
  return d.kind === "declaration";
}

function isOther(d: Declaration | Other): boolean {
  return d.kind === "other";
}

export function defined(statements: (Declaration | Other)[]): boolean {
  return statements.filter(isDeclaration).some((d) => d.body);
}

export function first(statements: readonly (Declaration | Other)[]): boolean {
  const found = statements.find(isDeclaration);
  return found ? found.body : false;
}

export function others(
  statements: (Declaration | Other)[],
): (Declaration | Other)[] {
  return statements.filter(isOther);
}
