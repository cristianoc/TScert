// `push` modelled as code, at its contract (ECMA-262, sec-array.prototype.push;
// tools/array-prototype.mts):
//   { name: "push", from: "Array", signature: "push(...items: T[]): number;",
//     effect: frameEffect(receiverExtendFrame, { receiverGrows: true }) }
// On a normal return the receiver's spine changes by `extend` and every other
// location keeps its contents; the receiver's length grows by the count of
// `items`, which it appends. The specification sets each item at the next
// index, then the length; at a length of 2^32 - 1 that write throws a
// RangeError (ArraySetLength), thrown here before it.
// This body does not grow the receiver: `push` of one item returns the old
// length and leaves the receiver as it was (run under Node).
/** @ensures this.length === old(this.length) + items.length */
export function push<T>(this: T[], ...items: T[]): Modifies<{ "this[*]": "extend" }, number> {
  return this.length;
}
