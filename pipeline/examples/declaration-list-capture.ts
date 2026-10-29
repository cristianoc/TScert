// A closure the first declarator's default creates captures the second
// declarator's binding, an early binding; the closure runs after the list,
// where the binding holds its value (under Node, `capture([])` returns 4).
export function capture(fs: readonly (() => number)[]): number {
  const [f = (): number => b] = fs, b: number = 2;
  return f() + b;
}
