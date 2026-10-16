// An element of an array `Array.isArray` finds in `unknown` is `unknown`, not
// the number TypeScript's `any[]` lets the program claim.
export function head(x: unknown): number {
  if (Array.isArray(x)) return x[0];
  return 0;
}
