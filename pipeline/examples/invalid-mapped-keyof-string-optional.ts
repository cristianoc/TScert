// Rule mapped-keyof-string: the field `a`, optional in X, is required in
// `KS<X>`; TypeScript rejects the empty object.
type KS<X> = { [K in keyof X & string]: X[K] };

export function missingRequired(): KS<{ a?: number }> {
  // @ts-expect-error Property 'a' is missing
  return {};
}
