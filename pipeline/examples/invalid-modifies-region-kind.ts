// A spine region at a path that is no collection path: `b` is declared an
// object with a number field, no array, null or undefined, and a region
// `b[*]` is well-formed only at a path whose declared type is a collection
// type (the note "Tolerant frames", §3, "Regions"). Refused at the
// declaration.
type Box = { n: number };
export function note(b: Box): Modifies<{ values: "keep"; spines: "keep"; "b[*]": "any" }, number> {
  return b.n;
}
