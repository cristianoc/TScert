// An overloaded call's result is the result of the overload it matches: a
// string argument gives a string, whatever the other overload returns.
declare function pick(x: number): number;
declare function pick(x: string): string;
export function wrong(): number {
  return pick("a");
}
