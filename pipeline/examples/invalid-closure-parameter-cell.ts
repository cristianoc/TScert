// A closure's assigned parameter that an inner closure writes is a cell: a
// call between the test and the read may replace what it holds, so the test
// does not narrow it. TypeScript keeps the narrowing across the call; under
// Node the read gives `undefined` where a string is returned.
type Expr = { kind: "paren"; inner: Expr } | { kind: "name"; text: string };

export const textOf = (e: Expr, other: Expr): string => {
  const reset = (): void => {
    e = other;
  };
  if (e.kind === "name") {
    reset();
    return e.text;
  }
  return "";
};
