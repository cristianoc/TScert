// A closure wider than the element calling a captured `let`, rebound before
// the `map` to a function shrinking the array: the result has a hole.
type F = { k: "f"; n: number };
type A = { k: "a"; s: string };
type T = A | F;

export function wrong(calls: F[]): string[] {
  let impl = (t: T): string => t.k;
  const name = (t: T): string => impl(t);
  impl = (t: T): string => {
    calls.pop();
    return t.k;
  };
  return calls.map(name);
}
