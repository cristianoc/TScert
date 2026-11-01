// A nested sparse array may contain a hook that shrinks the array map visits.
export function wrong(
  xs: number[],
  rows: readonly (readonly ({ toJSON(): string } | undefined)[] | undefined)[],
): number[] {
  return xs.map((x) => {
    JSON.stringify(rows);
    return x;
  });
}
