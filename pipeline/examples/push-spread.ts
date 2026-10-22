// `push` of spread arrays: a readable or dense store passes its elements at
// their type, so the call is at the receiver's own element type.
type Stmt = { k: "let"; name: string } | { k: "expr"; value: number };

class Gate {
  hoisted: Stmt[] = [];
}

export function hoist(gate: Gate, extra: readonly Stmt[], last: Stmt): number {
  const statements: Stmt[] = [];
  statements.push({ k: "let", name: "x" });
  gate.hoisted.push(...statements);
  gate.hoisted.push(...extra, last);
  return gate.hoisted.length;
}

// The receiver is the spread's source: its elements are read before `push`
// writes.
export function doubled(xs: number[]): number {
  xs.push(...xs);
  return xs.length;
}

// The spread's operand writes the receiver before `push` reads its length.
const drained = (xs: number[]): number[] => {
  const out: number[] = [];
  while (xs.length > 0) {
    const x = xs.pop();
    if (x !== undefined) out.push(x);
  }
  return out;
};

export function refilled(xs: number[]): number {
  xs.push(...drained(xs));
  return xs.length;
}

// An element type admitting `undefined` passes a hole as `undefined`.
export function holes(
  xs: (number | undefined)[],
  ys: (number | undefined)[],
): number {
  xs.push(...ys, ...[1, 2]);
  return xs.length;
}
