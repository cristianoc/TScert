// `Math.random()` reads no argument and writes nothing a program reaches:
// a `map` calling it stays dense.
export function rolls(sides: number[]): number[] {
  return sides.map((n) => Math.ceil(Math.random() * n));
}
