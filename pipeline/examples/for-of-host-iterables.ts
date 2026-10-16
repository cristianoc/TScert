// `for...of` over the host's iterables other than arrays: each loop steps
// the iteration intrinsic of its iterable's kind, which TypeScript's type of
// it picks (DESIGN.md, "Async and iteration"). A string yields its code
// points, a `Set` its elements, a `Map` a fresh `[key, value]` per entry, and
// `keys`, `values` and `entries` a host iterator of their collection. None of
// these iterators has a `return`, so a loop left early calls nothing.
export function codePoints(s: string): number {
  let n = 0;
  for (const c of s) {
    if (c === " ") continue;
    n = n + c.length;
  }
  return n;
}

export function sum(s: Set<number>): number {
  let total = 0;
  for (const x of s) total += x;
  return total;
}

export function firstLarge(s: Set<number>, fallback: number): number {
  for (const x of s) {
    if (x > 10) return x;
  }
  return fallback;
}

export function entries(m: Map<string, number>): number {
  let total = 0;
  for (const entry of m) {
    const pair: [string, number] = entry;
    total += pair[1];
  }
  return total;
}

export function keysUntil(m: Map<string, number>, stop: string): string {
  let out = "";
  for (const k of m.keys()) {
    if (k === stop) break;
    out = out + k;
  }
  return out;
}

export function values(m: Map<string, boolean>): number {
  let n = 0;
  for (const v of m.values()) if (v) n = n + 1;
  return n;
}

export function setEntries(s: Set<number>): number {
  let total = 0;
  for (const e of s.entries()) total += e[0] + e[1];
  return total;
}

export function literal(): number {
  let n = 0;
  for (const c of "abc")
    for (const x of new Set<number>([1, 2])) n = n + x + c.length;
  return n;
}
