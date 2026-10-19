// A regex pattern is read by its `Symbol.match`, `source` and `flags`, which
// an object meeting `RegExp` may hold as accessors (run under Node: the
// getter runs): `new RegExp` is stated at a string pattern.
export function copied(r: RegExp): RegExp {
  return new RegExp(r);
}
