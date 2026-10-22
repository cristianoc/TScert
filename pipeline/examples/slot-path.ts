// A member path whose root is a `let` held in a slot (HOST-FAMILIES.md,
// "Paths rooted at a slot"): a test of the path refines the read it made, a
// later read of the path is that value while the read links hold, and a
// write of the root ends them, as a test of the slot itself ends there.
type Expr =
  | { readonly kind: "paren"; readonly inner: Expr }
  | { readonly kind: "name"; readonly text: string }
  | { readonly kind: "index"; readonly object: Expr; readonly key: Expr };

// After the loop's last write, within one condition, as the front end's
// `memberMayBeWritten` tests an assignment's target.
export function namesKey(e: Expr, key: string): boolean {
  let target = e;
  while (target.kind === "paren") target = target.inner;
  return (
    target.kind === "index" &&
    !(target.key.kind === "name" && target.key.text !== key)
  );
}

// Tested in one statement and read in a later one: the entry holds the
// path's witness, linked to the slot.
export function keyText(e: Expr): string {
  let target = e;
  while (target.kind === "paren") target = target.inner;
  if (target.kind !== "index" || target.key.kind !== "name") return "";
  const text = target.key.text;
  target = e;
  return text;
}

// A write between two tests: the second test refines the read of the
// written value, which the read after it is.
export function retested(e: Expr, other: Expr): string {
  let target = e;
  if (target.kind === "index" && target.key.kind === "name") {
    target = other;
    if (target.kind === "index" && target.key.kind === "name")
      return target.key.text;
  }
  return "";
}
