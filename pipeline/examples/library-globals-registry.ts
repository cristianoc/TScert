// `Symbol.for` and `Symbol.keyFor`, methods of the global `Symbol`, read at
// their declared signatures.
function registered(key: string): symbol {
  return Symbol.for(key);
}

function keyOf(s: symbol): string | undefined {
  return Symbol.keyFor(s);
}
