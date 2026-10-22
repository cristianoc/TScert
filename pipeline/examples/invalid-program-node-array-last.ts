// A program's own interface named `NodeArray` is no compiler-API node list:
// its name grants nothing, and the read at `length - 1` of an empty one is
// `undefined`.
interface NodeArray {
  readonly length: number;
  readonly [index: number]: string;
}

export function last(xs: NodeArray): string {
  return xs[xs.length - 1];
}
