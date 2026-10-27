// A copy of an error does not take its `name`, which it inherits from
// `Error.prototype` (run under Node: the copy's `name` is `undefined`), though
// TypeScript types the copy with it.
function copy(e: Error): { name: string } {
  return { ...e };
}

export function main(): string {
  return copy(new Error("m")).name;
}
