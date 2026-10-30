// `Required` over an optional field whose type is a type parameter, without
// `exactOptionalPropertyTypes`: TypeScript takes `undefined` from the
// parameter's instance, a type no term states, and the reader refuses it.
export function get<T>(x: Required<{ b?: T }>): T {
  return x.b;
}
