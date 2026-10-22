// Where `b?.k === "d"` fails, `b` may be undefined: the false branch keeps
// it so.
type Node = { k: "d"; t: number } | { k: "e"; u: string };

export function wrong(b: Node | undefined): Node {
  if (b?.k === "d") return { k: "e", u: "" };
  // @ts-expect-error b is undefined where the chain is
  return b;
}
