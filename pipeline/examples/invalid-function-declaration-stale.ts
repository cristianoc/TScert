// TypeScript keeps a `let` narrowed across a call of a function declaration
// writing it (run under Node: a string returned at number). The `let` is a
// cell the declaration captures; after the call it is at its contract.
export function stale(): number {
  let v: number | string = 1;
  function bump(): void {
    v = "s";
  }
  if (typeof v === "number") {
    bump();
    return v;
  }
  return 0;
}
