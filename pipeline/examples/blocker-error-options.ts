// Error construction needs a contract for the cause options argument.
// Census functions:
// fragment-parse.mts#failingAsTool.
export function use(reason: unknown): void {
  throw new Error("failed", { cause: reason });
}
