// `{}` admits a string, which gives its code units at its indices:
// `{ 0: 1, ..."x" }` holds a string under `0`.
export function overIndex(s: {}): { 0: number } {
  return { 0: 1, ...s };
}
