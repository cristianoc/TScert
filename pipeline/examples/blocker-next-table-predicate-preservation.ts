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
    !isMap(type.result.name) ||
    type.result.args.length !== 2
  )
    throw Error("table");
  return type.result.args;
}
