// Clearing a narrowed module cell via a helper inside a `for...of` over a host
// iterable invalidates the fact for the next iteration: returning `lastReason`
// at `string` returns `null` under Node, and the verifier refuses it.
let lastReason: string | null = null;

function clearReason(): void {
  lastReason = null;
}

export function clearedDuringSetLoop(s: Set<number>, reason: string): string {
  lastReason ??= reason;
  for (const value of s) {
    if (value > 1) return lastReason;
    clearReason();
  }
  return "";
}
