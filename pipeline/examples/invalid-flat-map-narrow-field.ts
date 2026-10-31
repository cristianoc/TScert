// A record field typed `{…}[]` is given a writable array of a narrower
// element arm, which is refused as invariant; TypeScript accepts it
// covariantly.
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
  const fields = parts.flatMap((p) => (p.spread !== undefined ? [] : [p]));
  if (fields.length === parts.length) return { k: "alloc", fields };
  return null;
}
