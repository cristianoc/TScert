// A comparison with a value that may itself be undefined holds where both
// are: its true branch keeps `b` possibly undefined.
type Node = { k: "d"; t: number } | { k: "e"; u: string };

export function wrong(b: Node | undefined, c: "d" | undefined): Node {
  // @ts-expect-error b is undefined where c is
  if (b?.k === c) return b;
  return { k: "e", u: "" };
}
