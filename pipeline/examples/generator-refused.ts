// A generator's body stops at each `yield` and resumes there on the next
// call of `next`, which no term of the calculus expresses.
function* upTo(n: number): Generator<number> {
  for (let i = 0; i < n; i++) yield i;
}

export function count(n: number): number {
  let total = 0;
  for (const i of upTo(n)) total = total + i;
  return total;
}
