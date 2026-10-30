// A closure whose loop's test is the literal `true` exits only by
// returning or throwing: its inferred result is the returns' union, with
// no implicit `undefined`, for `while (true)` and for a `for` with a
// binding per iteration and no test.

export function use(limit: number): {
  first(): number;
  second(): string;
} {
  return {
    first: () => {
      let i = 0;
      while (true) {
        if (i > limit) return i;
        i++;
      }
    },
    second: () => {
      for (let i = 0, read = () => i; ; i++) {
        if (i > limit) return String(read());
        if (i > 100) throw new Error("too many");
      }
    },
  };
}
