// A comparison of an optional chain with a literal tests the receiver, then
// compares the receiver's reads: where the chain is not what `undefined`
// would give, the receiver is present and its field is what the test says.
type Node = { k: "d"; t: number } | { k: "e"; u: string } | { k: "f" };
type Opt = { v?: string | null };

// `===`: the true branch has the receiver at the arm the tag selects.
export function strict(b: Node | undefined): number {
  return b?.k === "d" ? b.t : 0;
}

// `!==`: past the early return, the receiver is that arm.
export function unequal(b: Node | undefined): number {
  if (b?.k !== "d") return 0;
  return b.t;
}

// The literal on the left.
export function literalFirst(b: Node | undefined): string {
  return "e" === b?.k ? b.u : "";
}

// `!= null`: the receiver is present and the field is neither null nor
// undefined.
export function loose(o: Opt | null): string {
  if (o?.v != null) return o.v;
  return "";
}

// `!== undefined`: the receiver is present, the field may be null.
export function defined(o: Opt | undefined): string | null {
  if (o?.v !== undefined) return o.v;
  return null;
}

// The false branch of `== null`: present, and the field holds a string.
export function absent(o: Opt | undefined): string {
  if (o?.v == null) return "";
  return o.v;
}

// As a value: `false` where the receiver is nullish.
export function value(b: Node | undefined): boolean {
  return b?.k === "e";
}

// The receiver found by `find`, which may be `undefined`.
export function found(xs: readonly Node[]): number {
  const b = xs.find((s) => s.k === "d");
  return b?.k === "d" ? b.t : 0;
}

// Two links:the receiver is present where the chain is a string.
type Outer = { inner: Node };
export function nested(o: Outer | undefined): Node {
  return o?.inner.k === "f" ? o.inner : { k: "f" };
}
