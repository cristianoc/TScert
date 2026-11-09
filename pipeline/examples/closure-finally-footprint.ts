// A closure whose body runs in a `try` with a `finally` claims the footprint
// its block and its finalizer stay within, where the finalizer only falls
// through or throws: a `map` callback calling it keeps its result dense, and a
// function calling it stays within a stated footprint.
// Census functions:
// fragment-classes.mts#classBody, fragment-classes.mts#classStmt.
type Scope = { depth: number[] };
export function measured(vs: string[], scope: Scope): number[] {
  const measure = (v: string): number => {
    scope.depth.push(1);
    try {
      if (v === "") throw new Error("empty");
      return v.length;
    } finally {
      scope.depth.push(0);
    }
  };
  return vs.map((v) => measure(v));
}
export function stated(
  v: string,
  scope: Scope,
): Modifies<{ values: "any"; stores: "grow" }, number> {
  const measure = (s: string): number => {
    scope.depth.push(1);
    try {
      return s.length;
    } finally {
      scope.depth.push(0);
    }
  };
  return measure(v);
}
