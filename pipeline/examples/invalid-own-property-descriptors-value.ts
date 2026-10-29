// A descriptor `Object.getOwnPropertyDescriptors` makes at a key the
// record's type does not state holds whatever the property holds,
// `unknown`, though TypeScript's `any` lets it be claimed a number: a
// record may own further keys (run under Node).
export function extra(o: { a: number }): number {
  return Object.getOwnPropertyDescriptors(o)["x"]?.value ?? 0;
}
