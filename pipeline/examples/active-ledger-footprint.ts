// tools/files.mts: insertion-ordered unique active records, composed through
// the existing native Set footprints. Generic callbacks retain their effects.
const active = new Set<number>();
function enter(ledger: number): Modifies<{ values: "any" }, number | null> {
  if (active.has(ledger)) return null;
  active.add(ledger);
  return ledger;
}
function leave(ledger: number | null): Modifies<{ values: "any" }, void> {
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
  run: () => Modifies<{ values: "any"; stores: "grow"; onThrow: true }, T>,
): Modifies<{ values: "any"; stores: "grow" }, T> {
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
