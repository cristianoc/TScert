// An object rest does not hold the keys the pattern names: `a` was taken.
function rest(x: { a: string; b: number }): { a: string } {
  const { a, ...others } = x;
  return others;
}
export function main(): string {
  return rest({ a: "a", b: 1 }).a;
}
