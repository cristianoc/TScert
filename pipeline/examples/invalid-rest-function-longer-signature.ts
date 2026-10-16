// A rest whose element is a string, where the further parameter is a number:
// the function returns the number at a string contract.
function firstMore(v: unknown, ...more: string[]): string {
  return more[0] ?? "";
}

export function wrong(): (s: string, i: number) => string {
  return firstMore;
}
