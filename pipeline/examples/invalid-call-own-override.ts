// A received function's `.call` is its own property where it owns one: the
// callable annotation constrains the function's invocation, not its
// properties. A `read` whose ordinary call returns a number may own a `call`
// returning a string, which this function then returns as a number.
class PrototypeReader {
  value: number = 1;
  read(): number {
    return this.value;
  }
}

type ReaderProperty = { readonly read: (this: PrototypeReader) => number };

export function copyReaderArgument(
  source: ReaderProperty,
  receiver: PrototypeReader,
): number {
  const copy = { ...source };
  return copy.read.call(receiver);
}
