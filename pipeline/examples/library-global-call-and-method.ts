// `Symbol` both called and read through its registry methods: each method's
// call is the intrinsic stating its step, and the global its call signature.
function both(key: string): symbol {
  const local: symbol = Symbol("local");
  return Symbol.for(key);
}

function described(s: symbol): string | undefined {
  const fresh = Symbol(1);
  return fresh === s ? undefined : Symbol.keyFor(s);
}
