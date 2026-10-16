// The contract proposed from the return is a list; a write of a string is
// refused at the contract, though the binding holds a list again before the
// return: `build(6)` returns null, and the string was written in between.
type List = null | { head: number; tail: List };

export function build(n: number): List {
  let r = null;
  for (let i = 0; i < n; i++) {
    r = { head: i, tail: r };
  }
  r = n > 5 ? "many" : r;
  r = null;
  return r;
}
