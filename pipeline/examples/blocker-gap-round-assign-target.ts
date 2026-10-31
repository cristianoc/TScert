// Object.assign target read after argument-array destructuring.
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
export function lower(
  args: readonly number[],
  read: (n: number) => number,
): number {
  if (args.length === 0) throw Error("target required");
  const [target, ...sources] = args;
  return read(target);
}
