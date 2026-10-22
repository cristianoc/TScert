// A key written, then given by a spread of a literal on one arm: the copy's
// key is either's, `{ name: number } | { name: string }`.
export function earlier(dots: boolean): string | number {
  const o = { name: "x", ...(dots ? { name: 1 } : {}) };
  return o.name;
}
