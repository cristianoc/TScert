// A conditional type alias with a bounded parameter: TypeScript computes
// `never` for `P<number>`, and the application keeps its obligation that
// `number` meets `string`.
type P<T extends string> = T extends "a" ? T : never;
export function f(x: P<number>): string {
  return x;
}
