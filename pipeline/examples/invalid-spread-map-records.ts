// Removing future input elements can leave holes in map's result.
type Part = { spread: number } | { name: string; e: number };
export function build(
  base: number,
  fields: { name: string; e: number }[],
): Part[] {
  return [
    { spread: base },
    ...fields.map(({ name, e }) => {
      fields.pop();
      return { name, e };
    }),
  ];
}
