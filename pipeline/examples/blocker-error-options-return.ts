// A return at the annotation `Error`: the error holds its `message` and the
// `name` `Error.prototype` gives it on its link, as TypeScript's `Error` is
// read.
// Census functions:
// fragment-parse.mts#failingAsTool.
export function use(): Error {
  return new Error("failed", { cause: "reason" });
}
