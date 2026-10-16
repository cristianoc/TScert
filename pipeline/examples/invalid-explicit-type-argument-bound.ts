// An explicit type argument must satisfy its binder's bound, as TypeScript
// requires (TS2344): `number` is not a `string`.
declare function pick<V extends string>(): V;

export function violated(): number {
  return pick<number>();
}
