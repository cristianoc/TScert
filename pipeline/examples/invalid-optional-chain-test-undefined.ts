// `b?.k === undefined` holds where `b` is undefined: its true branch keeps
// `b` possibly undefined.
type Node = { k?: "d"; t: number };

export function wrong(b: Node | undefined): Node {
  // @ts-expect-error b is undefined where the chain is
  if (b?.k === undefined) return b;
  return b;
}
