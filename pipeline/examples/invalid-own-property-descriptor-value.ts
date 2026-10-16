// A descriptor's `value` is whatever the property holds, `unknown`, though
// TypeScript's `any` lets it be claimed a number.
export function first(o: object): number {
  return Object.getOwnPropertyDescriptor(o, "a")?.value ?? 0;
}
