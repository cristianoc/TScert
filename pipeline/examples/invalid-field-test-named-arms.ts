// After the join, the arms no test dropped remain: `constructor` holds no
// `fields`.
type Term =
  | { k: "object"; fields: number[] }
  | { k: "atom"; name: string }
  | { k: "constructor"; arity: number };

function afterJoin(first: Term | undefined): number {
  if (first && first.k === "atom") return first.name.length;
  if (first === undefined) return 0;
  return first.fields.length;
}
