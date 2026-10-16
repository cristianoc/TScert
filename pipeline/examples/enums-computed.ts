// Enums with a member whose value is known only at run time: each such
// member's initializer runs in order, a read of an earlier member reading its
// value, and `%Enum:E%` builds the object, adding the reverse mapping at keys
// known only at run time. The object type states the members only, one known
// only at run time at `number`, and `E` is the union of the members' values,
// `number` for such a member.
function one(): number {
  return 1;
}
enum G {
  A = ".".length,
  B = 4,
  C = A,
  D = G.B + G["A"],
  E = one(),
}
function computedMember(): number {
  return G.A;
}
function literalMember(): 4 {
  return G.B;
}
function referenceMember(): number {
  return G.C + G.D + G.E;
}
function anyNumber(n: number): G {
  return n;
}
function widen(x: G): number {
  return x;
}
function object(): typeof G {
  return G;
}
function memberType(): G.A {
  return G.E;
}
