// `super.m(…)` in a class extending `Error` calls a member of
// `Error.prototype` the model does not state: refused.
class Described extends Error {
  describe(): string {
    return super.toString();
  }
}
export function text(): string {
  return new Described("x").describe();
}
