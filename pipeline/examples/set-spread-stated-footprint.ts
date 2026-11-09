// A native `Set` spread into an array literal steps the host's iterator,
// which runs no client code and writes only its own position: the spread
// is within a stated `{value: any, store: grow}`, as type-term.mts's
// `visitType` extends the binder names in scope. A `ReadonlySet` would admit
// a program object whose iterator runs code (`invalid-readonly-set-has-effect`).
type Term = { names: string[]; parts: Term[] };

export function visit(
  term: Term,
  seen: (
    term: Term,
    bound: ReadonlySet<string>,
  ) => Modifies<{ values: "any"; stores: "grow" }, void>,
  bound: Set<string> = new Set(),
): Modifies<{ values: "any"; stores: "grow" }, void> {
  seen(term, bound);
  const inner = new Set([...bound, ...term.names]);
  for (const part of term.parts) visit(part, seen, inner);
}
