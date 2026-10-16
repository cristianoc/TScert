// Each cell consed onto `result` holds the one before it: the union of what
// is written into it grows with every step, and no evolved type settles. No
// use reads its whole value at a type, so no use states a contract either.
export function build(n: number): number {
  let result = null;
  for (let i = 0; i !== n; i++) {
    result = { head: i, tail: result };
  }
  return result === null ? 0 : result.head;
}
