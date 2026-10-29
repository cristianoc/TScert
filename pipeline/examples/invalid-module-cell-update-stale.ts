// TypeScript keeps a module cell narrowed by `??=` across a call of a
// function that writes it (run under Node: `null` is returned at string);
// after the call the cell is at its contract.
let reason: string | null = null;

function clear(): void {
  reason = null;
}

export function retire(why: string): string {
  reason ??= why;
  clear();
  return reason;
}
