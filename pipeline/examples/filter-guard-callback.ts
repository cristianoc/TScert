// `filter` at a guard closure keeps the values the guard answers `true` for,
// each at the promise's type: the closures over its result read their
// parameter there, a nested optional call included, as the front end's
// `readScope` reads its declarations.
type Modifier = { kind: "declare" | "export" };
type Declaration = {
  kind: "declaration";
  name: string;
  body: boolean;
  modifiers?: Modifier[];
};
type Other = { kind: "other"; name: string };

export function defined(
  statements: (Declaration | Other)[],
  name: string,
): boolean {
  const named = statements.filter(
    (d): d is Declaration => d.kind === "declaration" && d.name === name,
  );
  return (
    named.some((d) => d.body) &&
    !named.some((d) => d.modifiers?.some((m) => m.kind === "declare"))
  );
}

// The result is the promise's type, read where a wider one is expected too.
export function declarations(
  statements: readonly (Declaration | Other)[],
): readonly Declaration[] {
  return statements.filter((d): d is Declaration => d.kind === "declaration");
}

// A guard binding the index too, and one promising `never`: nothing is kept.
export function evenStrings(xs: (string | number)[]): string[] {
  return xs.filter((x, i): x is string => i % 2 === 0 && typeof x === "string");
}

export function none(xs: (string | number)[]): never[] {
  return xs.filter((x): x is never => false);
}

// A guard writing the receiver it filters: each kept value was a string
// when the guard answered, and stays one whatever the guard writes later.
export function overwriting(xs: (string | number)[]): string[] {
  return xs.filter((x): x is string => {
    xs[0] = 0;
    return typeof x === "string";
  });
}
