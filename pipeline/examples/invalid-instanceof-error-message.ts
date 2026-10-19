// `instanceof Error` says nothing of the operand's fields: an object gets
// `Error.prototype` without `Error` constructing it, its `message` any value
// (run under Node: a number). The read after the test is refused.
export function text(e: unknown): string {
  return e instanceof Error ? e.message : "";
}
