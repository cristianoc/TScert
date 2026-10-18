// A recursive constant that shadows a module function of its name: its
// literal's reads are its self entry, never the module function.
function visit(n: number): number {
  return n;
}
export function f(xs: number[]): number {
  const visit = (n: number): number => (n > 0 ? visit(n - 1) : 0);
  return visit(xs.length);
}
export function g(): number {
  return visit(1);
}
