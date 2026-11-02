// Immutable callable facts survive expression arms at their checked types.
export function choices(input: number | null): (number | null)[] {
  const term = (n: number): number => n;
  const both = (n: number | null): number | null => n && term(n);
  const either = (n: number | null): number => n || term(1);
  const fallback = (n: number | null): number => n ?? term(1);
  const conditional = (n: number | null): number | null =>
    n === null ? null : term(n);
  const offered: (n: number, ...more: unknown[]) => number = term;
  return [both(input), either(input), fallback(input), conditional(input)];
}

export function boundRecord(
  input: { name: string; bound: number | null },
  kept: number[],
): { name: string; bound: number | null } {
  const term = (n: number): Within<{ value: "any"; store: "grow" }, number> => {
    kept.push(n);
    return n;
  };
  const param = (p: {
    name: string;
    bound: number | null;
  }): { name: string; bound: number | null } => ({
    ...p,
    name: p.name,
    bound: p.bound && term(p.bound),
  });
  const offered: (
    n: number,
    ...more: unknown[]
  ) => Within<{ value: "any"; store: "grow" }, number> = term;
  return param(input);
}
