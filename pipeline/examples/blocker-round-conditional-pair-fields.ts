// A conditional pair inferred as an array, destructured into required record fields.
// Census functions:
// fragment-expressions.mts#expr
// fragment-expressions.mts#objectFields
// fragment-expressions.mts#optionalChain
// fragment-expressions.mts#optionalMethodCall
// fragment-expressions.mts#wrappedMethodCall
// fragment-expressions.mts#chainLink
// fragment-expressions.mts#update
// fragment-expressions.mts#template
// fragment-expressions.mts#binary
// fragment-expressions.mts#lambda
type Term = { k: "atom"; name: string };
type Expr = { k: "withValue"; functionType: Term; bagType: Term };
export function wrap(flag: boolean, left: Term, right: Term): Expr {
  const [functionType, bagType] = flag ? [left, right] : [right, left];
  return { k: "withValue", functionType, bagType };
}
