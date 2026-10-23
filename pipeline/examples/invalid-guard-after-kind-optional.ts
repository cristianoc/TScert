// An absent kind reads as undefined on both tests; that observation does
// not establish the required field promised by the result.
type Receiver = { kind?: "a" } | { kind: undefined };

export function wrong(node: Receiver): { kind: undefined } {
  if (node.kind === "a") return { kind: undefined };
  if (node.kind === undefined) return node;
  return { kind: undefined };
}
