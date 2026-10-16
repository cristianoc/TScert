// join calls an element's toString without arguments, violating this callback contract.
export function wrong(seen: { value: number }): number {
  const xs: { toString: (x: number) => string }[] = [
    {
      toString: (x: number): string => {
        seen.value = x;
        return "x";
      },
    },
  ];
  xs.join();
  return seen.value;
}
