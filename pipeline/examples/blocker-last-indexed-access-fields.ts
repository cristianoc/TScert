// An indexed access's projection over a record's fields and a union's parts,
// as `indexedAccess` in computed-types.mts writes it: the guard keeping the
// found fields names its parameter at the array's element type, and the
// union's parts are projected into a fresh array by a loop, whose pushes
// leave no hole whatever the projection does.
// Census functions: computed-types.mts#indexedAccess.
import type { TypeTerm } from "../../tools/declaration-types.mts";

type ObjectTerm = Extract<TypeTerm, { k: "object" }>;

const union = (parts: TypeTerm[]): TypeTerm => {
  const [only] = parts;
  return parts.length === 1 && only ? only : { k: "union", parts, span: [0, 0] };
};

export function fields(object: ObjectTerm, keys: TypeTerm[]): TypeTerm | null {
  const parts = keys.map((key) => {
    if (key.k !== "literal" || key.name !== "string") return null;
    const field = object.fields.find((f) => f.name === key.text);
    return field ? field.type : null;
  });
  const found = parts.filter((p: TypeTerm | null): p is TypeTerm => p !== null);
  return found.length === parts.length ? union(found) : null;
}

export function project(object: TypeTerm, read: (t: TypeTerm) => TypeTerm): TypeTerm {
  if (object.k !== "union") return read(object);
  const projected: TypeTerm[] = [];
  for (const part of object.parts) projected.push(read(part));
  return union(projected);
}
