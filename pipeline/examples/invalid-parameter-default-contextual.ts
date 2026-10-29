// An assigned closure parameter with a default and no annotation: its
// contract is the type its context gives, `"a" | "b"`, which an unannotated
// `let` would widen to `string`. Refused at the gate.
export const pick: (s?: "a" | "b") => string = (s = "a") => {
  // @ts-expect-error "c" is not "a" | "b"
  s = "c";
  return s;
};
