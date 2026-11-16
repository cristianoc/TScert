type Hook = (
  n: number,
  read: (n: number) => Modifies<{ values: "any"; spines: "grow" }, string>,
) => Modifies<{ values: "any"; spines: "grow" }, string>;

export function argumentsFor(xs: number[]): Parameters<Hook> {
  return [
    0,
    (n: number): string => {
      xs.pop();
      return `${n}`;
    },
  ];
}
