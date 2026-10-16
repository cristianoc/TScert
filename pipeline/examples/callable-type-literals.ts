// A type literal with call signatures is a callable, in an ambient
// function's result as in a declaration: a string test leaves it, and it is
// called.
declare function one(): { (x: number): string } | string;
export function called(): string {
  const v = one();
  return typeof v === "string" ? v : v(1);
}
