// `f.call(r)` calls the standard `Function.prototype.call` where `f` is a
// known local function: every value of a local `let` (its initializer and
// each assignment) is one, and a member of an object built by a spread is the
// member its source holds. A closure captures the `let`.
type Reader = { value: number };

function readOwn(this: Reader): number {
  return this.value;
}

function captured(source: Reader): () => number {
  let alias: { readonly read: (this: Reader) => number } = { read: readOwn };
  alias = { read: readOwn };
  return () => {
    const copy = { ...alias };
    return copy.read.call(source);
  };
}

function reassigned(source: Reader): number {
  let f = readOwn;
  f = function (this: Reader): number {
    return this.value + 1;
  };
  return f.call(source);
}
