// A closure wider than the element that shrinks the array it is mapped over:
// `map` leaves a hole where the removed element was, so the result is no
// `string[]` of strings.
type F = { k: "f"; n: number };
type A = { k: "a"; s: string };
type T = A | F;

export function wrong(calls: F[]): string[] {
  const name = (t: T): string => {
    calls.pop();
    return t.k;
  };
  return calls.map(name);
}
