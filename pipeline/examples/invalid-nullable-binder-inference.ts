// `A := number` from `number | null`: the result is a number, not a string.
declare function unwrapInline<A>(value: A | null): A;
declare const nn: number | null;
export function bad(): string {
  return unwrapInline(nn);
}
