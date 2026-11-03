// Census functions: fragment-statements.mts#switchStmt,#statements.
// A closure declared before the closure that calls it, inside a function
// stating `{value: any, store: grow}`: each is a constant initialized
// before any call, so the caller reads the callee at the footprint its body
// shows, and the function meets its statement.
export function plainLabels(
  labels: readonly string[],
  known: ReadonlySet<string>,
): Within<{ value: "any"; store: "grow" }, boolean> {
  const member = (u: string): boolean =>
    u.startsWith("E.") && labels.includes(u.slice(2));
  const plain = (u: string): boolean =>
    u === "null" || /^-?[0-9]+$/.test(u) || member(u);
  return labels.every((u) => plain(u) || known.size === 0);
}
