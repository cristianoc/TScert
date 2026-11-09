// Census functions: fragment-statements.mts#hoisting,#statements.
// A `forEach` callback writing a fresh array to a field of a captured
// record, inside a function stating `{value: any, store: grow}`: the field
// holds an array object, a value, so the write changes one location holding
// a value, the callback is within `{value: any, store: keep}` beside its
// pushes, and the function meets its statement.
type Scope = { pending: string[] };
export function collect(
  scope: Scope,
  names: readonly string[],
): Modifies<{ values: "any"; stores: "grow" }, string[]> {
  const parts: string[] = [];
  names.forEach((n) => {
    scope.pending = [];
    scope.pending.push(n);
    parts.push(...scope.pending);
  });
  return parts;
}
