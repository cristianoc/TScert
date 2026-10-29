// An optional chain of named reads on a name, read for its truthiness alone
// (a condition, an operand of `!`, of `&&` or `||` in a condition, the left
// operand of `||`): truthy, the receiver is present and its field is
// truthy, so a discriminant tested through the chain selects the arm. The
// census functions it stands for: fragment-parse.mts#lowerFile,
// fragment-classes.mts#classBody and #classStmt (`found?.ok ? found.value
// : null`, `result?.ok && typeof result.value !== "number" ? … : null`).
// Each run under Node.
type Answered<T> = { readonly ok: true; readonly value: T } | { readonly ok: false; readonly refused: string };

// A conditional's test: the arm where `ok` is true.
export function pick(m: Map<string, Answered<number>>, k: string): number | null {
  const found = m.get(k);
  return found?.ok ? found.value : null;
}

// The left operand of `&&` in a conditional's test, then a test of the
// field the first selected.
export function literal(result: Answered<number | { literal: string }> | undefined): string | null {
  return result?.ok && typeof result.value !== "number" ? result.value.literal : null;
}

// An `if`, its negation, and the left operand of `||` in a condition.
export function early(found: Answered<string> | undefined): string {
  if (!found?.ok) return "";
  return found.value;
}

export function either(found: Answered<string> | null, other: boolean): string {
  if (found?.ok || other) return "";
  return found === null ? "none" : found.refused;
}

// As a value, `&&` keeps the chain's own value, `undefined` where the
// receiver is nullish; the left operand of `||` gives its value where truthy.
export function kept(found: { readonly ok: true } | undefined): true | undefined {
  return found?.ok && true;
}

export function first(found: { readonly name: string } | undefined): string {
  return found?.name || "anonymous";
}
