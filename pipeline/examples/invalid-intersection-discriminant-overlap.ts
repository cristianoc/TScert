// `E & { k: X }` read at `at`. With X `"callback"`, the arm
// `"call" | "callback"` meets it and has no `at`: refused, as TypeScript
// refuses it (a value of that arm reads `undefined`). With `"optional"`, no
// other arm meets it: the twin, whose claims `pipeline/test.mts` checks
// against the refused source, with the claimed discriminant `"callback"`.
type Span = [number, number];
type E =
  | { k: "id"; pos: Span; name: string }
  | { k: "call" | "callback"; pos: Span; callee: E; receiver: E }
  | { k: "optional"; pos: Span; at: Span; receiver: E; body: E };
export function at(chain: E & { k: "callback" }): Span {
  return chain.at;
}
