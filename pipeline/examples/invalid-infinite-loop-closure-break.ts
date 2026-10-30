// A closure whose loop's test is the literal `true` and whose body holds a
// reachable `break` completes: its body ends in `return undefined`, and
// its result is `number | undefined`, outside the stated `number`.
export function use(limit: number): { first(): number } {
  return {
    first: () => {
      let i = 0;
      while (true) {
        if (i > limit) break;
        if (i > 9) return i;
        i++;
      }
    },
  };
}
