// Callbacks calling library globals at primitives, where each converts or
// compares without running client code and writes nothing: each call states
// heap preservation, so the callbacks do and `map`'s result is dense.
export function spaces(ts: string[]): number[] {
  return ts.map((t, i) => i - Number(t === " "));
}

export function labels(ns: number[]): string[] {
  return ns.map((n) => String(n) + "!");
}

export function signed(ns: number[]): boolean[] {
  return ns.map((n) => !Object.is(n, -0));
}
