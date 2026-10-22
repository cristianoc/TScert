export function flat(
  x: (() => number) & ((n: number) => number) & { tag: string },
): { tag: string } {
  return { ...x };
}
export function reordered(
  x: ((n: number) => number) & { tag: string } & (() => number),
): { tag: string } {
  return { ...x };
}
type Tagged = (() => number) & { tag: string };
type Counted = ((n: number) => number) & { count: number };
export function callablePair(x: Tagged & Counted): {
  tag: string;
  count: number;
} {
  return { ...x };
}
