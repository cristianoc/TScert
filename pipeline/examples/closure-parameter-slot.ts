// A closure's assigned parameter that no closure writes, and no closure
// created before one of its writes mentions, is a slot of the closure's
// activation, as a function's is: a test of the object it holds narrows it
// until the next write, which rebinds it at what it writes.

type Expr =
  | { kind: "paren"; inner: Expr }
  | { kind: "name"; text: string }
  | { kind: "call"; callee: Expr; args: Expr[] };

const isParen = (e: Expr): e is Extract<Expr, { kind: "paren" }> =>
  e.kind === "paren";

// A tag test in a loop's condition, the write in its body: each iteration's
// test narrows what the previous write stored.
export const unwrap = (e: Expr): Expr => {
  while (e.kind === "paren") e = e.inner;
  return e;
};

// A user guard, then tests after the loop; a recursive closure.
export function names(root: Expr): string[] {
  const found: string[] = [];
  const visit = (e: Expr): void => {
    while (isParen(e)) e = e.inner;
    if (e.kind === "name") found.push(e.text);
    else if (e.kind === "call") {
      visit(e.callee);
      e.args.forEach((a) => visit(a));
    }
  };
  visit(root);
  return found;
}

// A test, then a write of one arm, read at that arm.
type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; side: number };
export const area = (s: Shape): number => {
  if (s.kind === "circle") return 3 * s.radius * s.radius;
  s = { kind: "square", side: s.side * 2 };
  return s.side;
};

// A closure created after the last write reads the value it captured.
export const later = (e: Expr): (() => string) => {
  while (e.kind === "paren") e = e.inner;
  if (e.kind !== "name") return () => "";
  return () => e.text;
};
