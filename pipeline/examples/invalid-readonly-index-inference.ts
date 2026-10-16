type Data = null | boolean | number | string | { readonly [key: string]: Data };
function checked<T extends Data>(value: T): T {
  return value;
}
export function invalid(): Data {
  // @ts-expect-error A function-valued field violates the Data bound.
  return checked({ x: () => true });
}
