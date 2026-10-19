// A field test keeps or drops each arm of a named union wherever the name
// occurs in the tested type: beside arms of it a join left there, and inside
// another named union.
type Term =
  | { k: "object"; fields: number[] }
  | { k: "atom"; name: string }
  | { k: "constructor"; arity: number };

function afterConjunction(parts: Term[]): number {
  const [first, ...rest] = parts;
  if (first && !rest.length && first.k === "constructor") return first.arity;
  if (!first || first.k !== "object") return 0;
  return first.fields.length;
}

function afterJoin(first: Term | undefined): number {
  if (first && first.k === "atom") return first.name.length;
  if (first === undefined) return 0;
  if (first.k === "constructor") return first.arity;
  return first.fields.length;
}

type Leaf = { tag: 1; text: string };
type Pair = { tag: 2; left: number } | { tag: 3; right: number };
type Tree = Leaf | Pair;

function nested(t: Tree): number {
  if (t.tag === 1) return t.text.length;
  if (t.tag === 2) return t.left;
  return t.right;
}
