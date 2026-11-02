// Census functions: fragment-expressions.mts#expr,#objectFields,#optionalChain,
// #optionalMethodCall,#wrappedMethodCall,#chainLink,#update,#template,#binary,#lambda.
type E = { k: "id" };
export function wrap(args: E[]): { object: E } {
  if (!args[0]) throw Error("empty");
  return { object: args[0] };
}
