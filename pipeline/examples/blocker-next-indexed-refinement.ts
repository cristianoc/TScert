// Census functions: fragment-expressions.mts#expr,#objectFields,#optionalChain,
// #optionalMethodCall,#wrappedMethodCall,#chainLink,#update,#template,#binary,#lambda.
type E = { k: "id" };
export function wrap(args: E[]): { object: E } {
  const object = args[0];
  if (!object) throw Error("empty");
  return { object };
}
