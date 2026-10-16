// A written field meets each arm of the expected union only where its value
// does: `k` may be `false`, which the arm with `b` does not admit.
type AB = { a: number } | { b: string };
type Tagged = { a: number; k: boolean } | { b: string; k: true };

export function tag(x: AB, k: boolean): Tagged {
  return { ...x, k };
}
