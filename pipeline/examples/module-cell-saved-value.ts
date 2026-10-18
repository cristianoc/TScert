// A value read from a module cell and held in a constant keeps that value
// across a later write of the cell, which a call makes.
let mode: number | string = 0;

function reset(): void {
  mode = "s";
}

export function saved(): number {
  const before = mode;
  reset();
  return typeof before === "number" ? before : 0;
}
