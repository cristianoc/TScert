// A negated test first in a disjunction: each operand is dispatched on its
// truth where the ones before it failed (SOURCE-ELABORATION.md,
// "Conditions"). Where the disjunction holds, `m.n` may have decided it, so
// `m.q` may be undefined: `len({ kind: "method", n: 1 })` throws a
// TypeError under Node.
type M =
  | { readonly kind: "method"; readonly n?: number; readonly q?: string }
  | { readonly kind: "prop" };

export function len(m: M): number {
  if (!(m.kind === "method") || m.n || m.q) {
    return m.kind === "method" ? m.q!.length : 0;
  }
  return 0;
}
