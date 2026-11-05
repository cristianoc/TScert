// A `let` a closure assigns stays a cell: a test of the object it holds does
// not narrow it, since the call in between may replace it.
type U = { kind: "a"; name: string } | { kind: "b"; n: number };
export function reassigned(p: U, q: U): string {
  let u = p;
  const reset = (): void => {
    u = q;
  };
  if (u.kind === "a") {
    reset();
    return u.name;
  }
  return "";
}
