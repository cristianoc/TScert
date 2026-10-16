// `Record<"a" | "b", number>` has both keys as required fields: an object
// without `b` would read `undefined` where a number is promised.
function partial(): Record<"a" | "b", number> {
  return { a: 1 };
}
