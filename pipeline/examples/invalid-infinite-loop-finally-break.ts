// A `break` in a `finally` overrides the `return` of its `try`: the loop
// whose test is the literal `true` completes, and the closure returns
// `undefined`, outside the stated `number`.
export function use(stop: boolean): { first(): number } {
  return {
    first: () => {
      while (true) {
        try {
          return 1;
        } finally {
          if (stop) break;
        }
      }
    },
  };
}
