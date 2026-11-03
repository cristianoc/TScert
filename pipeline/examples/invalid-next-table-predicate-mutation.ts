// A table classifier whose predicate states no effect: the predicate may
// replace the reference it was given, so the result read after its call is
// at its declared union. Run under Node, `mutate` below makes `table` return
// `undefined` as its `number[]`.
// Census: tools/compiler-api.mts#tableReading.
type Term =
  | {
      k: "function";
      result: { k: "reference"; name: string; args: number[] } | { k: "other" };
    }
  | { k: "other" };
export function table(type: Term, isMap: (name: string) => boolean): number[] {
  if (
    type.k !== "function" ||
    type.result.k !== "reference" ||
    !isMap(type.result.name)
  )
    throw Error("table");
  return type.result.args;
}
export function mutate(): number[] {
  const type: Term = {
    k: "function",
    result: { k: "reference", name: "m", args: [1, 2] },
  };
  return table(type, () => {
    type.result = { k: "other" };
    return true;
  });
}
