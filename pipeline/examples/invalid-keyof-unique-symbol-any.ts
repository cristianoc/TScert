// A symbol is not a key of a promise: `keyof Promise<number>` holds one
// symbol, `Symbol.toStringTag`, and not every symbol.
function anySymbol(s: symbol): keyof Promise<number> {
  return s;
}
