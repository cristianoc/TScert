// Module functions passed by name as `map` callbacks: each binds one
// parameter where `map` passes three, discarding the others, so its slot
// meets the callback's signature at its own footprint, and the results are
// dense.
function escaped(s: string): string {
  return s.replace(/&/g, "&amp;");
}

function width(s: string): number {
  return s.length;
}

export function escapedAll(xs: string[]): string[] {
  return xs.map(escaped);
}

export function widths(xs: string[]): number[] {
  return xs.map(width);
}

// No expected result fixes `map`'s result binder: the function's own result
// does.
export function joinedWidths(xs: string[]): string {
  return xs.map(width).join(",");
}
