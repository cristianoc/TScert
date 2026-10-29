// A parameter typed `(...args: never) => unknown` is every function: it
// admits no call, so the body only tests it; any function is passed to it.
function isCode(f: (...args: never) => unknown): boolean {
  return typeof f === "function";
}
function twice(n: number): number {
  return n * 2;
}
export function checked(): boolean {
  return isCode(twice) && isCode((s: string): string => s);
}
