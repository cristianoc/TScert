// A concrete class method declaring a rest parameter collects further actuals
// into the rest array, so it does not gain a `...unknown[]` extension:
// passing a number at position 2 throws `TypeError` on `toUpperCase` under Node.
class WithRest {
  m(a: number, ...rest: string[]): string {
    const first = rest[0];
    return first !== undefined ? first.toUpperCase() : "none";
  }
}

interface TwoNum {
  m(a: number, b: number): string;
}

export function bad(): string {
  const t: TwoNum = new WithRest();
  return t.m(1, 42);
}
