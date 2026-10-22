// An alias of an intersection of function types, met with a record: the
// verifier reads the alias's meet as empty, where the same operands written
// in the annotation are one overloaded callable carrying the field
// (`spread-intersection-callable-grouping`).
type Calls = (() => number) & ((n: number) => number);
export function grouped(x: Calls & { tag: string }): { tag: string } {
  return { ...x };
}
