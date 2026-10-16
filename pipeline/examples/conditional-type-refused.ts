// A conditional type: the declaration reader has no reading of
// `T extends U ? X : Y`, so it refuses the declaration rather than read it in
// part.
type Conditional<T> = T extends boolean ? number : string;
export function pick(value: Conditional<boolean>): number {
  return value;
}
