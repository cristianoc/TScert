/**
 * `unknown` is semantic top: every value may inhabit it, and membership
 * permits no read, call or test through it. A `void` result forgets its
 * guarantee about the value into the same top, while staying a distinct
 * source type: the callback still runs, and its effects still happen.
 */
/** A void callback: invoked for its effects; the private scalar's fact survives. */
function privateScalar(x: number | null, action: () => void): number {
  if (x === null) return 0;
  action();
  return x;
}
/** A void function completes without a return: its value is undefined. */
function guardedLoopRead(x: string | null, again: boolean): void {
  while (x !== null && again) {
    const text: string = x;
    x = null;
  }
}
/** A void function whose loop counts. */
function unchangedLoopRead(x: string | null, again: boolean): void {
  if (x !== null) {
    let count: number = 0;
    while (again) {
      const text: string = x;
      count += 1;
    }
  }
}
/** An unknown value passes through unexamined. */
function passUnknown(x: unknown): unknown {
  const y = x;
  return y;
}
