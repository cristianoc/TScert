// An array assignment writing fields: the right side first, then, for each
// target in turn, its reference (the receiver, then the key), its position's
// read and its default, then the write.

// A field, a local and a rest into a field: the right side holds the values
// read before any write.
function swapInto(
  pair: { first: number; second: number },
  rest: { items: number[] },
): number {
  let local = 0;
  [pair.first, local, ...rest.items] = [pair.second, pair.first, 3, 4];
  return pair.first + local + rest.items.length;
}

// The key is evaluated before the default: the log reads "kd".
function keyBeforeRead(log: { order: string }, box: { slot: string }): string {
  [
    box[(log.order = log.order + "k") === "" ? "slot" : "slot"] = (log.order =
      log.order + "d"),
  ] = [undefined];
  return log.order;
}
