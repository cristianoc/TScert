// With `exactOptionalPropertyTypes`, `Required<{ b?: string | undefined }>`
// is `{ b: string | undefined }`: its field is not a `string`.
export function read(x: Required<{ b?: string | undefined }>): string {
  return x.b;
}
