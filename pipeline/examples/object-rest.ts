// An object pattern's rest is a fresh object holding the source's other own
// enumerable properties: a merge onto a fresh object that drops the keys
// the pattern's properties name.
function rest(x: { a: string; b: number; c: boolean }): {
  b: number;
  c: boolean;
} {
  const { a, ...others } = x;
  return others;
}
function parameter({ a, ...others }: { a: number; b: string }): string {
  return others.b + a;
}
export function main(): string {
  return parameter({ a: 1, b: "x" }) + rest({ a: "a", b: 1, c: true }).b;
}
