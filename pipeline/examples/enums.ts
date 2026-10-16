// Enums: the module constant bound to the object TypeScript's emit creates,
// each member a readonly field at its value, and a numeric member's reverse
// mapping from its value's key to its name. `E` is the union of its members'
// literal types, `E.A` a member's, `typeof E` the object's; a `const enum`'s
// reads are its values.
enum E {
  A,
  B,
}
enum F {
  A,
  B,
}
enum Offset {
  A = 5,
  B,
}
enum Negative {
  A = -1,
  B,
}
enum SE {
  A = "a",
  B = "b",
}
enum Het {
  N = 0,
  S = "s",
}
enum Frac {
  A = 1.5,
  B,
}
enum Same {
  A = 0,
  B = 0,
}
enum Arith {
  A = 1,
  B = A + 1,
  C = "x" + "y",
}
const enum CE {
  A,
  B = 7,
}
function member(): E {
  return E.A;
}
function literal(): E.B {
  return 1;
}
function widen(x: E): number {
  return x;
}
function crossEnum(x: E): F {
  return x;
}
function autoIncrement(): 6 {
  return Offset.B;
}
function negative(): 0 {
  return Negative.B;
}
function stringMember(): "a" {
  return SE.A;
}
function literalToStringEnum(): SE {
  return "b";
}
function heterogeneous(x: Het): 0 | "s" {
  return x;
}
function reverse(): "A" {
  return E[0];
}
function reverseFraction(): "B" {
  return Frac[2.5];
}
function reverseLastWins(): "B" {
  return Same[0];
}
function byName(): 0 {
  return E["A"];
}
function folded(): "xy" {
  return Arith.C;
}
function object(o: typeof E): 1 {
  return o.B;
}
function whole(): typeof E {
  return E;
}
function inlined(): 7 {
  return CE.B;
}
