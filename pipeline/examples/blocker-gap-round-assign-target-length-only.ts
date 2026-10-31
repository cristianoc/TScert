// The Object.assign target is checked directly after destructuring.
// The compiler-node-array site uses the same check in fragment-expressions.mts#expr.
export function lower(
  args: readonly number[],
  read: (n: number) => number,
): number {
  if (args.length === 0) throw Error("target required");
  const [target, ...sources] = args;
  if (target === undefined) throw Error("target required");
  return read(target);
}
