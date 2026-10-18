// A field's equality with a string literal is a fact of the field where its
// type is a union holding objects too (parsed JSON): a later read of the
// field is of the literal, from a record's field and a dictionary's entry,
// through one test or either of two.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function kindOf(c: { kind: Json }): "a" | null {
  let mode: "a" | null = null;
  if (c.kind === "a") mode = c.kind;
  return mode;
}
export function codeKind(c: {
  [key: string]: Json;
}): "construct" | "sloppy" | null {
  let mode: "construct" | "sloppy" | null = null;
  if (c.kind === "construct" || c.kind === "sloppy") mode = c.kind;
  return mode;
}
