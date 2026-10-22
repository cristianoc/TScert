// A key required by one operand and narrowed by another's optional field:
// the meet is the required key at the narrower type, which no one field
// states (`Src.sure` gives a key at one of the source's fields).
export function copied(x: { tag: number; k: string } & { k?: "a" }): {
  tag: number;
  k: string;
} {
  return { ...x };
}
