// tools/files.mts: insertion-ordered unique active records, composed through
// the existing native Set footprints. Generic callbacks retain their effects.
const active = new Set<number>();
function enter(
  ledger: number,
): Within<{ value: "any"; store: "keep" }, number | null> {
  if (active.has(ledger)) return null;
  active.add(ledger);
  return ledger;
}
function leave(
  ledger: number | null,
): Within<{ value: "any"; store: "keep" }, void> {
  if (ledger !== null) active.delete(ledger);
}
export function withLedger<T>(ledger: number, run: () => T): T {
  const entered = enter(ledger);
  try {
    return run();
  } finally {
    leave(entered);
  }
}
export function kept<T>(
  ledger: number,
  run: () => Within<{ value: "any"; store: "grow"; onThrow: true }, T>,
): Within<{ value: "any"; store: "grow" }, T> {
  const entered = enter(ledger);
  try {
    return run();
  } finally {
    leave(entered);
  }
}
export function shrinks(xs: number[]): number | undefined {
  return withLedger(1, () => xs.pop());
}
