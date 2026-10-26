// A return at the annotation `Error` needs the modeled error to meet
// TypeScript's `Error`, which declares `name`.
// Census functions:
// fragment-parse.mts#failingAsTool.
export function use(): Error {
  return new Error("failed", { cause: "reason" });
}
