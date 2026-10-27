// An error inherits `name` from `Error.prototype`, a string, which the model
// states on the error's link. The calculus keeps an error from
// `{ name?: number }`: an object type establishes an optional field it does
// not state only where its key bounds exclude that key and the prototype key,
// which `object`'s do not. Under Node, `wrong()` returns "Error".
function hide(e: Error): object {
  return e;
}

function read(v: { name?: number }): number {
  return v.name ?? 0;
}

export function wrong(): number {
  return read(hide(new Error("m")));
}
