// A module cell tested against `null`, then a construction at a signature
// keeping the heap, `new Uint8Array(n)`: Lean's `call-keep` keeps every
// heap fact across it, a construction's as a call's, so the cell keeps its
// narrowing. Census functions: none; found reducing pretext's
// line-breaks.ts#unpackClasses.
let runs: number[] | null = null;

function first(a: number[], b: number): number {
  return a.length + b;
}

export function unpack(n: number): number {
  if (runs === null) return 0;
  const bytes = new Uint8Array(n);
  return first(runs, bytes.length);
}
