// Each merged member keeps its own type.
interface Pair {
  left: number;
}
interface Pair {
  right: string;
}
export function wrong(p: Pair): number {
  return p.right;
}
