// A key one operand states as a method and another as a data field: the
// object may hold it on its prototype, which a spread does not copy, so the
// copy does not state it. `Object.assign(new Counter(), { tag: "t" })` is of
// the intersection, TypeScript admitting it since `Counter` has `next`; its
// copy has no `next` (run under Node).
class Counter {
  count: number = 0;
  next(): number {
    return this.count + 1;
  }
}
export function copied(c: Counter & { next: () => number; tag: string }): {
  next: () => number;
  tag: string;
} {
  return { ...c };
}
