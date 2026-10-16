// A `let` held in a slot holds a written object at its declared type's arms,
// as TypeScript narrows a declared type on assignment: after the join of a
// literal with the optional field and one without it, a read of the
// optional field is at the declared field, `number | undefined`.
export function joined(reset: boolean): number {
  let r: { a: number; b?: number } = { a: 1, b: 2 };
  if (reset) {
    r = { a: 0 };
  }
  return r.a + (r.b ?? 0);
}

export function rewritten(): number {
  let r: { a: number; b?: number } = { a: 1, b: 2 };
  r = { a: 0 };
  return r.a + (r.b ?? 0);
}
