// Where `x ?? 0` takes `x`, its values are the bound's other than null and
// undefined: a string among them.
export function present<T extends number | string | null>(x: T): number {
  // @ts-expect-error Type 'string | number' is not assignable to type 'number'.
  return x ?? 0;
}
