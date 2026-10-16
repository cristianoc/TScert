// `{}` holds primitives too, which are not objects.
export function bad(x: {}): object {
  return x;
}
