// A `Set<number>` is no `Set<number | string>`: `add` would put a string in
// it. TypeScript's bivariant method parameters admit the assignment.
function widen(s: Set<number>): Set<number | string> {
  return s;
}
