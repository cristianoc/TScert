// A program's own `unique symbol` is not `Symbol.toStringTag`, the one
// symbol key of a promise.
const tag: unique symbol = Symbol();
function ownSymbol(): keyof Promise<number> {
  return tag;
}
