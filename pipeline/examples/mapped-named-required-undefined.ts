// `Required` at a named type over an optional field whose type holds
// `undefined`, without `exactOptionalPropertyTypes`: as at a record written
// in place, TypeScript takes `undefined` from the field's type.
interface Options {
  b?: string | undefined;
}
export function make(): Required<Options> {
  return { b: "b" };
}

export function read(x: Required<Options>): string {
  return x.b;
}
