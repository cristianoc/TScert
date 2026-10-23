// A condition's tests refine where they run, and a later step acts on what
// they found: a call in the right operand of `&&` may write the field the
// left operand tested, so past it nothing is known of the field's contents,
// while the union arm the test selected stays a lifetime fact. A write of
// a local past its test leaves the local what was written.
type T =
  | { k: "atom"; name: string }
  | { k: "union" | "intersection"; parts: T[] };

export function parameterCall(operand: T, fail: (m: string) => never, binder: (t: T) => boolean): void {
  if (operand.k === "union" && binder(operand)) fail("a union holding a binder");
}

export function localCall(operand: T, fail: (m: string) => never): void {
  const binder = (t: T): boolean => t.k === "union" && t.parts.some(binder);
  if (operand.k === "union" && binder(operand)) fail("a union holding a binder");
  if (operand.k !== "union" || binder(operand)) return;
  fail("a union without a binder");
}

export function reassigned(x: string | number): boolean {
  return typeof x === "string" && (x = 0, x === 0);
}
