// A closure is offered a signature binding more parameters than it does
// wherever it flows, not only as an argument: its code ignores the extra
// actuals, so Lean checks its body at the longer signature too.
export function annotatedBinding(): (a: number, b: string) => number {
  const one: (a: number) => number = (a: number) => a;
  const two: (a: number, b: string) => number = one;
  return two;
}

export function annotatedLiteral(): (a: number, b: string) => void {
  const f: (a: number, b?: string) => void = (_a: number) => {};
  const g: (a: number, b: string) => void = f;
  return g;
}

export function returned(): (a: number, b: string) => number {
  const one = (a: number) => a + 1;
  return one;
}
