// A fresh flatMap result states the writable element contract of its
// destination field, keeping the input objects and their order.
// Census functions:
// fragment-expressions.mts#expr, fragment-expressions.mts#binary.
type Part =
  | { name: string; e: number; computed?: true; spread?: never }
  | { spread: number; name?: never };
type Alloc = {
  k: "alloc";
  fields: { name: string; e: number; computed?: true }[];
};

export function alloc(parts: Part[]): Alloc | null {
  const fields = parts.flatMap<Alloc["fields"][number]>((p) =>
    p.spread !== undefined ? [] : [p],
  );
  if (fields.length === parts.length) return { k: "alloc", fields };
  return null;
}
