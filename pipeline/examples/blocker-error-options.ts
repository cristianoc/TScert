// `new Error(message, { cause })`: the options argument states `cause`, at
// which `HasProperty` and `Get` run no code.
// Census functions:
// fragment-parse.mts#failingAsTool.
export function use(reason: unknown): void {
  throw new Error("failed", { cause: reason });
}
