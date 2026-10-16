// A script without a "use strict" directive is sloppy code. Its call wraps a
// primitive receiver in an object, so `this` is no string: TypeScript types
// `self` at `string`, and `self.call("a")` returns a `String` object.
function self(this: string): string {
  return this;
}

function caller(): string {
  return self.call("a");
}
