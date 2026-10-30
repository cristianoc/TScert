// Without `exactOptionalPropertyTypes`, `Required<{ b?: string | undefined }>`
// is `{ b: string }`: a record holding `undefined` at `b` does not meet it.
export function make(): Required<{ b?: string | undefined }> {
  const b: string | undefined = undefined;
  return { b };
}
