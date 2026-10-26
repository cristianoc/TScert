// `Required` at a named type over an optional field whose type may hold
// `undefined`: TypeScript's meaning depends on `exactOptionalPropertyTypes`,
// and the reader refuses the field, as at a record written in place.
interface Options {
  b?: string | undefined;
}
export function make(): Required<Options> {
  return { b: "b" };
}
