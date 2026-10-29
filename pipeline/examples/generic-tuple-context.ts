// An array literal at a generic parameter placing the binders at tuple
// positions is a tuple there, each position at its element's type, widened:
// a pair at `readonly [K, V]`, pairs at `readonly (readonly [K, V])[]`, a
// Map's entries, and a callback's result reaching such a parameter.
function second<K, V>(entry: readonly [K, V]): V {
  return entry[1];
}

function lastValue<K, V>(entries: readonly (readonly [K, V])[]): V | undefined {
  const [first] = entries;
  return first?.[1];
}

export function pair(n: number): number {
  return second(["a", n]) + 1;
}

export function pairs(n: number): number {
  return (lastValue([["a", n]]) ?? 0) + 1;
}

export function mapped(xs: readonly number[]): number {
  return (lastValue(xs.map((x) => ["a", x])) ?? 0) + 1;
}

export function entries(n: number, s: string): number {
  const m = new Map([[s, n]]);
  m.set(s.toUpperCase(), n + 1);
  for (const v of m.values()) return v + 1;
  return 0;
}
