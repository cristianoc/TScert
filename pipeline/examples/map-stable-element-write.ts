// A write of an array's element at a literal index keeps every dense
// prefix: into a listed position's location, or a fresh location the store
// lists. `map` callbacks writing a pair's element, a tuple's optional
// position, the mapped array's first element and a nested pair's element by
// compound assignment are preserving, and the results are dense.
export function relabel(xs: string[], pair: [string, string]): string[] {
  return xs.map((x: string): string => {
    pair[1] = x;
    return pair[0];
  });
}
export function extend(
  xs: number[],
  triple: [number, number, number?],
): number[] {
  return xs.map((x: number): number => {
    triple[2] = x;
    return triple[0] + x;
  });
}
export function firsts(xs: string[]): string[] {
  return xs.map((x: string): string => {
    xs[0] = x;
    return x;
  });
}
export function appendAll(entries: [string, string][], xs: string[]): number[] {
  return xs.map((x: string): number => {
    const last = entries[0];
    if (last !== undefined) last[1] += x;
    return entries.length;
  });
}
function setSecond(pair: [string, string], s: string): number {
  pair[1] = s;
  return 0;
}
function setThird(triple: [number, number, number?], x: number): number {
  triple[2] = x;
  return 0;
}
export function seconds(xs: string[], pair: [string, string]): number[] {
  return xs.map((x: string): number => setSecond(pair, x));
}
export function thirds(
  xs: number[],
  triple: [number, number, number?],
): number[] {
  return xs.map((x: number): number => setThird(triple, x));
}
