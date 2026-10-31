// Census functions: fragment-classes.mts#classBody, fragment-classes.mts#classStmt.
// The map builds records at the element type of an array literal spread.
type Part = { spread: number } | { name: string; e: number };
export function build(
  base: number,
  fields: { name: string | { private: string }; e: number }[],
  fail: () => never,
): Part[] {
  return [
    { spread: base },
    ...fields.map(({ name, e }) => ({
      name: typeof name === "string" ? name : fail(),
      e,
    })),
  ];
}
