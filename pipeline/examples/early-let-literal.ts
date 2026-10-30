// A closure reading a `let` declared after it, the `let` unannotated and
// initialized by a literal: the binding is early, and its stated type is
// the literal's primitive type, TypeScript's declared type for it. Census
// functions: fragment-statements.mts#markEarly (`let statementStart = -1`
// read in `visit`) and the functions whose slices include it, functionDecl,
// protocolPattern, switchStmt, controlStmt and hoistTarget among them.
export function starts(lengths: readonly number[]): number[] {
  const out: number[] = [];
  const visit = (n: number): void => {
    out.push(start + n);
  };
  let start = -1;
  for (const n of lengths) {
    start = n;
    visit(n);
  }
  return out;
}

// A `let` nothing assigns, read through the earlier closure.
export function unassigned(): number {
  const read = (): number => x;
  let x = -1;
  return read();
}

// The other primitive families: a string, a Boolean and a bigint.
export function families(): string {
  const label = (): string => `${name}:${on}:${big}`;
  let name = "a";
  let on = true;
  let big = -2n;
  name = name + "b";
  on = !on;
  big = big * 3n;
  return label();
}

// The closure run before the declaration: the read throws a ReferenceError.
export function tooEarly(): number {
  const read = (): number => x;
  const value = read();
  let x = 1;
  return value + x;
}
