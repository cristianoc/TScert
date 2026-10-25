// A declared array read in a generic finally block needs its array method view
// retained.
// Census functions:
// files.mts#withLedger.
declare const values: { value: number }[];
export function use<T>(run: () => T): T {
  try {
    return run();
  } finally {
    values.splice(0, 1);
  }
}
