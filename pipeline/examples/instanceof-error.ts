// `e instanceof Error` walks `e`'s prototype chain, which runs no code: a
// Boolean.
export function isError(e: unknown): boolean {
  return e instanceof Error;
}
