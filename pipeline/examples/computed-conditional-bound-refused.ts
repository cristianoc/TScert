// A conditional type alias with a bounded parameter: TypeScript computes
// `never` for `P<number>`, and the application, with its obligation that
// `number` meets `string`, would be gone.
type P<T extends string> = T extends "a" ? T : never;
export function f(x: P<number>): string {
  return x;
}
