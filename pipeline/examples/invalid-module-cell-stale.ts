// TypeScript keeps a module cell narrowed across a call of a function that
// writes it (run under Node: the string is returned at number); after the
// call the cell is at its contract.
let mode: number | string = 0;

function reset(): void {
  mode = "s";
}

export function stale(): number {
  if (typeof mode === "number") {
    reset();
    return mode;
  }
  return 0;
}
