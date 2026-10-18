// A string gives its code units at its indices: `{ 0: 1, ..."x" }` holds a
// string under `0`.
export function overIndex(s: string | { b: number }): { 0: number } {
  return { 0: 1, ...s };
}
