// An unannotated constant holding a `map` result, first used as a spread
// part of an array literal passed where `Term[]` is expected: the result is
// built at `Term[]`, as type-term.mts's `classInstance` joins a method's
// later overloads to the earlier ones. At its callback's own record type the
// invariant array would not meet that contract.
type Term = { k: "function"; arity: number; receiver: string | null };

function joined(terms: Term[]): number {
  return terms.length;
}

export function join(earlier: Term[], forms: Term[], receiver: string): number {
  const added = forms.map((f) => ({ ...f, receiver }));
  return joined([...earlier, ...added]);
}
