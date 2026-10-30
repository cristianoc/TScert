// A loop whose test is the literal `true` completes through a `break`
// leaving it: the function may then return `undefined`, outside its
// stated result. A `break` of a nested loop, or of a `switch` in the
// body, leaves only that statement.
export function wrong(n: number): boolean {
  for (;;) {
    for (const k of [1, 2]) if (k > n) break;
    switch (n) {
      case 0:
        break;
      default:
        if (n > 9) return true;
    }
    if (n < 0) break;
    n++;
  }
}
