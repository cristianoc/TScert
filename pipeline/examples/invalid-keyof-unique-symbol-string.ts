// `keyof [number]` holds every number and the names a tuple has, not the
// string "1": a one-position tuple names no second position.
const second: keyof [number] = "1";
