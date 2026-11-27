// Excluding a non-empty literal (`s !== "a"`) leaves `""` admitted, so
// `s.length` may be 0 and `s.codePointAt(0)!` returns `undefined` at `number`
// (run under Node with `""`).

export function firstAfterNotA(s: string): number {
  if (s !== "a") {
    const n = s.length;
    if (n >= 0) return s.codePointAt(0)!;
  }
  return 0;
}
