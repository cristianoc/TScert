// A closure whose loop exits only by returning a tuple has the tuple as its
// inferred result, with no implicit undefined.
// Census functions:
// fragment-statements.mts#sites.
export function use(): {
  span(): Modifies<{ values: "any"; stores: "grow" }, [number, number]>;
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
