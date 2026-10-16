// A member known only at run time is a number, not the literal a reader of
// the source might expect: "ab".length is 2, and the function promises 1.
enum G {
  A = "ab".length,
}
function wrong(): 1 {
  return G.A;
}
