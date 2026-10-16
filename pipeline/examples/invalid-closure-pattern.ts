// A closure parameter's pattern reads an optional field at its type or
// `undefined`.
export function optionalField(): number {
  const f = ({ x }: { x?: number }): number => x;
  return f({});
}
