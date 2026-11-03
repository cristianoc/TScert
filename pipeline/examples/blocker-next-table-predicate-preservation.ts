// A table classifier keeps the nested reference it checks: the predicate
// states that it changes no location, so the reference read before its call
// is the one read after it.
// Census: tools/compiler-api.mts#tableReading.
type Term =
  | {
      k: "function";
      result: { k: "reference"; name: string; args: number[] } | { k: "other" };
    }
  | { k: "other" };
export function table(
  type: Term,
  isMap: (name: string) => Within<{ value: "keep"; store: "keep" }, boolean>,
): number[] {
  if (
    type.k !== "function" ||
    type.result.k !== "reference" ||
    !isMap(type.result.name) ||
    type.result.args.length !== 2
  )
    throw Error("table");
  return type.result.args;
}
