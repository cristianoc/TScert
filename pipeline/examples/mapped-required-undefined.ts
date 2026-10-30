// `Required` over an optional field whose type holds `undefined`, in a
// project without `exactOptionalPropertyTypes`: TypeScript takes `undefined`
// from the field's type, written or as `void`, so the field is a `string`.
export function make(): Required<{ b?: string | undefined }> {
  return { b: "b" };
}

export function read(x: Required<{ b?: string | void }>): string {
  return x.b;
}

export function none(x: Required<{ b?: undefined; c: number }>): number {
  return x.c;
}
