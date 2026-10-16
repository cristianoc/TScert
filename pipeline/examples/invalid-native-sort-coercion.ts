// Default sort calls client conversion methods without their required arguments.
export function wrong(seen: { value: number }): number {
  const entry = {
    toString: (x: number): string => {
      seen.value = x;
      return "x";
    },
  };
  const xs = [entry, entry];
  xs.sort();
  return seen.value;
}
