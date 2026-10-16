// A member known only at run time writes its reverse mapping at its value's
// key: NaN's is "NaN", which replaces the member named NaN. TypeScript types
// `Q.NaN` as 1; the object holds "X" there. A member named by a canonical
// numeric string beside a member known only at run time is refused.
enum Q {
  NaN = 1,
  X = "x".charCodeAt(1),
}
function one(): 1 {
  const q = Q;
  return q.NaN;
}
