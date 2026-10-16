// A conditional type TypeScript computes to a primitive is that primitive:
// `Conditional<"x">` is `string`, no value of `number`.
type Conditional<T> = T extends boolean ? number : string;
export function pick(value: Conditional<"x">): number {
  return value;
}
