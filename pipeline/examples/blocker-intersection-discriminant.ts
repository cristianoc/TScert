// A union intersected with one arm's discriminant: `E & { k: "optional" }`
// holds the arm whose `k` is `"optional"` alone, whose fields are read. Every
// other arm states `k` at literals disjoint from `"optional"`, a tag set
// (`"call" | "bind"`) among them, and holds no value; a numeric discriminant
// alike.
// Census functions:
// fragment-expressions.mts#expr, fragment-expressions.mts#binary,
// fragment-expressions.mts#lambda, fragment-expressions.mts#objectFields,
// fragment-expressions.mts#optionalMethodCall,
// fragment-expressions.mts#chainLink, fragment-expressions.mts#chainReads,
// fragment-expressions.mts#chainComparison, fragment-expressions.mts#chainTest.
type Span = [number, number];
type E =
  | { k: "id"; pos: Span; name: string }
  | { k: "this"; pos: Span }
  | { k: "call" | "bind"; pos: Span; callee: E; receiver: E }
  | { k: "optional"; pos: Span; at: Span; receiver: E; body: E };
function reread(chain: E & { k: "optional" }): E | null {
  const receiver = chain.receiver;
  if (receiver.k !== "id" && receiver.k !== "this") return null;
  return receiver.k === "id"
    ? { k: "id", pos: chain.at, name: receiver.name }
    : { k: "this", pos: chain.at };
}
export function use(e: E): E | null {
  return e.k === "optional" ? reread(e) : e;
}
// A numeric discriminant alike: the arm whose `tag` is `2` alone.
type N =
  | { tag: 1; a: string }
  | { tag: 2 | 3; b: number }
  | { tag: 4; b: string };
export function bOf(x: N & { tag: 2 }): number {
  return x.b;
}
