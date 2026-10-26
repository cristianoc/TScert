// An error inherits `name` from `Error.prototype`, which the model's error
// does not hold. The calculus keeps an error from `{ name?: number }`: the
// error `new Error(m)` builds does not meet `Error`, which states `name`, and
// an object type establishes an optional field it does not state only where
// its key bounds exclude that key and the prototype key, which `object`'s do
// not. Under Node, `wrong()` returns "Error".
function hide(e: Error): object {
  return e;
}

function read(v: { name?: number }): number {
  return v.name ?? 0;
}

export function wrong(): number {
  return read(hide(new Error("m")));
}
