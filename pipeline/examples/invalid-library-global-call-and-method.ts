// `Symbol.keyFor` gives `undefined` for a symbol the registry does not hold.
function described(s: symbol): string {
  const fresh = Symbol("fresh");
  return Symbol.keyFor(fresh === s ? fresh : s);
}
