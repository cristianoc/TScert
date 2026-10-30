// `Required` over an optional field whose type holds `undefined`, in a
// project with `exactOptionalPropertyTypes`: TypeScript keeps the field's
// type, so the field is present and may hold `undefined`, written in place,
// through an alias, at a named type or as a type parameter.
type Missing = undefined;
interface Options {
  b?: string | undefined;
}
export function make(): Required<{ b?: string | undefined }> {
  return { b: undefined };
}

export function named(): Required<Options> {
  return { b: undefined };
}

export function aliased(x: Required<{ b?: string | Missing }>): string | undefined {
  return x.b;
}

export function get<T>(x: Required<{ b?: T }>): T {
  return x.b;
}
