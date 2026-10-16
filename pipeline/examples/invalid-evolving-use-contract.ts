// The contract proposed from the return is a list; the last write is a
// string when `n > 5`, which `build(6)` returns. The write is refused at the
// contract.
type List = null | { head: number; tail: List };

export function build(n: number): List {
  let r = null;
  for (let i = 0; i < n; i++) {
    r = { head: i, tail: r };
  }
  r = n > 5 ? "many" : r;
  return r;
}
