// Error construction needs a contract for the cause options argument.
// Census functions:
// fragment-parse.mts#failingAsTool.
export function use(): Error {
  return new Error("failed", { cause: "reason" });
}
