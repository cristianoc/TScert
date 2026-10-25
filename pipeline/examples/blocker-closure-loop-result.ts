// A closure whose loop exits only by returning a tuple needs its inferred
// result to exclude implicit undefined.
// Census functions:
// fragment-statements.mts#sites.
export function use(): {
  span(): Within<{ value: "any"; store: "grow" }, [number, number]>;
} {
  let i = 0;
  return {
    span: () => {
      for (;;) {
        if (++i > 0) return [0, i];
      }
    },
  };
}
