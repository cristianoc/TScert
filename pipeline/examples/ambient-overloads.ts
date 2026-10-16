// A function declared with overloads is callable at each of them: its value
// meets every overload, so each call is checked against the one it matches.
declare function pick(x: number): number;
declare function pick(x: string): string;
export function text(): string {
  return pick("a");
}
export function count(): number {
  return pick(1);
}
