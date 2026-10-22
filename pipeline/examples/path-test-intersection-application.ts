// A truthiness test of a member of a binding whose type is an intersection
// with a generic application among its operands, `Param<Term> & { … }`:
// the test refines the path's read, which a read of the same path reads
// again, for a member of either operand, in a callback past a call between
// two tests. A failed test keeps a falsy member's defined values.
type Param<T> = { name: string; bound: T | null };
type Term =
  | { readonly k: "leaf"; readonly n: number }
  | {
      readonly k: "scheme";
      readonly binders: (Param<Term> & { default: Term | null })[];
    };

export function count(term: Term): number {
  if (term.k === "leaf") return term.n;
  let total = 0;
  const visit = (part: Term): void => {
    total = total + count(part);
  };
  term.binders.forEach((binder) => {
    if (binder.bound) visit(binder.bound);
    if (binder.default) visit(binder.default);
  });
  return total;
}

export function defaultOf(
  binder: Param<Term> & { default: Term | null },
): Term {
  if (binder.default) return binder.default;
  return { k: "leaf", n: 0 };
}

export function boundOr(
  binder: Param<number> & { default: number | null },
): number {
  if (binder.bound) return binder.bound;
  return binder.bound ?? -1;
}
