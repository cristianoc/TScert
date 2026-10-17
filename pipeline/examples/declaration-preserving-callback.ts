// Function declarations whose bodies read, compare and call only what
// preserves the heap: each declaration's signature states heap preservation,
// its own unit certifies it, and a `map` callback calling it preserves the
// heap, so the result is dense. One calls another, one calls itself, and one
// has a parameter default, evaluated in its body.
function isEq(t: string): boolean {
  return t === "=";
}

function marked(t: string): boolean {
  return isEq(t) || t.startsWith("!");
}

function depth(s: string): number {
  return s.startsWith("(") ? 1 + depth(s.slice(1)) : 0;
}

function padded(s: string, fill: string = " "): string {
  return fill + s + fill;
}

export function marks(ts: string[]): boolean[] {
  return ts.map((t) => marked(t));
}

export function depths(ts: string[]): number[] {
  return ts.map((t) => depth(t));
}

export function pads(ts: string[]): string[] {
  return ts.map((t) => padded(t) + padded(t, "|"));
}
