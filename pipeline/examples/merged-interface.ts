// An interface declared twice is one interface with both declarations'
// members, as TypeScript merges it.
interface Pair {
  left: number;
}
interface Pair {
  right: string;
}
export function right(p: Pair): string {
  return p.right;
}
