// TypeScript admits a type literal at an index signature its fields fit (an
// implicit index signature); a value of it may carry other keys of any
// type.
export function asDictionary(x: { readonly a: number }): {
  readonly [k: string]: number;
} {
  return x;
}
