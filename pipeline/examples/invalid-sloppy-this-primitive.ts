// A script without a "use strict" directive is sloppy code. Its call wraps a
// primitive receiver in an object, so `this` is no string: TypeScript types
// `this` at `string`, and `sloppySelf.call("a")` returns a `String` object.
function sloppySelf(this: string): string {
  return this;
}

function caller(): string {
  return sloppySelf.call("a");
}
