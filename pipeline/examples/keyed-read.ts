// A key of several string or number singletons reads the member each names:
// the key is tested against each singleton in turn, and the last needs no
// test, since the key is one of them.
function pick(s: "f" | "g", x: { f: number; g: number }): number {
  return x[s];
}
function pickOptional(
  s: "f" | "g",
  x: { f?: number; g: number },
): number | undefined {
  return x[s];
}
function numbered(i: 0 | 1, x: { 0: string; 1: string }): string {
  return x[i];
}
enum E {
  A,
  B,
}
function reverse(i: 0 | 1): "A" | "B" {
  return E[i];
}
