// Rule mapped-keyof-string: `{ [K in keyof X & string]: X[K] }` is not
// homomorphic in TypeScript. A field optional in X is required, holding
// undefined; a readonly field is writable; a string index absorbs the fields.
type KS<X> = { [K in keyof X & string]: X[K] };

export function optionalBecomesRequired(): KS<{ a?: number }> {
  return { a: undefined };
}

export function readonlyBecomesWritable(o: KS<{ readonly a: number }>): number {
  o.a = 2;
  return o.a;
}

export function indexAbsorbsFields(): KS<{ [k: string]: number; a: number }> {
  return {};
}
