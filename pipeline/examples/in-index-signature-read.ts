// A read after a passed `"k" in x` test where `x`'s type states `k` by a
// string index signature is an ordinary read at the index's value type,
// the form of `decodeCode`'s optional `kind` in tools/calculus.mts
// (census functions calculus.mts#termsOf, #decodeCode, #decodeTerm and
// control-flow.mts#decodeNode).
type Json =
  | null
  | boolean
  | number
  | string
  | readonly Json[]
  | { readonly [key: string]: Json };

export function modeOf(c: {
  readonly [key: string]: Json;
}): "construct" | "sloppy" | null {
  let mode: "construct" | "sloppy" | null = null;
  if ("kind" in c) {
    if (c.kind === "construct" || c.kind === "sloppy") mode = c.kind;
    else throw Error("invalid code kind");
  }
  return mode;
}

export function kindOf(c: { readonly [key: string]: Json }): Json {
  return "kind" in c ? c.kind : null;
}
