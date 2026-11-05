// `Error.prototype.toString`, which reads the instance's `name` and
// `message`, is a member the model does not state: refused.
export function text(): string {
  return new Error("x").toString();
}
