type Hook = (
  n: number,
  read: (n: number) => Within<{ value: "any"; store: "grow" }, string>,
) => Within<{ value: "any"; store: "grow" }, string>;

export function argumentsFor(xs: number[]): Parameters<Hook> {
  return [
    0,
    (n: number): string => {
      xs.pop();
      return `${n}`;
    },
  ];
}
