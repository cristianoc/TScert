// The well-known symbols of the global `Symbol`, read at `symbol` through the
// reviewed overlay: which symbol each is, is not read.
function wellKnown(): symbol[] {
  const iterator: symbol = Symbol.iterator;
  return [
    iterator,
    Symbol.asyncIterator,
    Symbol.hasInstance,
    Symbol.toPrimitive,
    Symbol.toStringTag,
  ];
}
// As an element key, `o[Symbol.iterator]` is the named read of the key that
// symbol is, the one `[Symbol.iterator]` names in a type.
function iterated(o: { [Symbol.iterator]: () => number }): number {
  return o[Symbol.iterator]();
}
