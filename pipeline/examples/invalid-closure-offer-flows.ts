// TypeScript's unsound pair: a closure reading an optional second string is
// held at `(a: number) => number`, then used where a number is passed second.
// Its code reads that parameter, so no longer signature is offered, and the
// binding is only its annotation.
export function bad(): (a: number, b: number) => number {
  const f: (a: number) => number = (a: number, b?: string) =>
    b === undefined ? a : b.length;
  const g: (a: number, b: number) => number = f;
  return g;
}
