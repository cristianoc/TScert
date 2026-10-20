// A closure's assigned parameter held in a slot: a write between the test and
// the read rebinds it at what it writes, so the test's refinement ends there
// and the read is of the written union's member, which one arm lacks
// (TypeScript also refuses it, TS2339). Under Node the read gives
// `undefined` where a string is returned.
type Expr = { kind: "paren"; inner: Expr } | { kind: "name"; text: string };

export const textOf = (e: Expr, other: Expr): string => {
  if (e.kind === "name") {
    e = other;
    return e.text;
  }
  return "";
};
