// An array literal right of `??`, where no type is expected, is built at
// the left's array type, as TypeScript types it: the fresh `[[]]` and its
// inner `[]` take the elements' contracts, so `map` reads one array type.
type Term = { readonly k: string };

export function forms(
  alternatives: Term[][] | null,
  params: readonly Term[],
): Term[][] {
  return (alternatives ?? [[]]).map((positions) => [...params, ...positions]);
}

export function lengths(alternatives: number[][] | null): number[] {
  const all = alternatives ?? [[]];
  return all.map((positions) => positions.length);
}

export function next(values: number[] | null): number[] {
  return (values ?? [1]).map((v) => v + 1);
}
