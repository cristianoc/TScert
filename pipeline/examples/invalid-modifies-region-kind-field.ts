// A spine region read through a field whose declared type is no collection
// type: `h.at` is a number, so `h.at[*]` names no array's spine and is not a
// well-formed region (the note "Tolerant frames", §3, "Regions"). Refused at
// the declaration.
type Holder = {
  /** @stable */
  readonly at: number;
};
export function note(h: Holder): Modifies<{ values: "keep"; spines: "keep"; "h.at[*]": "any" }, number> {
  return h.at;
}
