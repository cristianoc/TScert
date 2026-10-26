// `Required` over an optional field whose type may hold `undefined`: without
// `exactOptionalPropertyTypes` TypeScript takes `undefined` from it, with it
// TypeScript keeps it. The reader refuses the field.
export function make(): Required<{ b?: string | undefined }> {
  return { b: "b" };
}
