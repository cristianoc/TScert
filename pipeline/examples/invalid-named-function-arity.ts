// A module function meets a longer signature only where its own parameters
// accept the leading actuals, and only when it has no rest parameter, which
// would collect the further actuals instead of discarding them.
function collects(_a: number, ...rest: string[]): string {
  const first = rest[0];
  return first === undefined ? "none" : first.toUpperCase();
}
export function widen(): (a: number, b: number) => string {
  return collects;
}
