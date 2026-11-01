// Census: tools/claim-text.mts#bareAtomText and #atomText, through typeText,
// printType, liftClause, liftSignatures, liftType, liftLabels, treeAtom and lift.
// Finite conversion alone does not establish that the JSON field is text.
type JsonValue =
  | null
  | boolean
  | number
  | string
  | readonly JsonValue[]
  | { readonly [key: string]: JsonValue };
function describe(atom: {
  readonly a: JsonValue;
  readonly v: JsonValue;
}): string {
  if (
    (atom.a === "numberlit" || atom.a === "numlit") &&
    typeof atom.v === "string" &&
    Number.isFinite(Number(atom.v))
  )
    return atom.v;
  return "«type»";
}
