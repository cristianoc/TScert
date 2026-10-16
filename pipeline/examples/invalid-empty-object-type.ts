// `{}` is every value but `null` and `undefined`.
export function bad(x: number | undefined): {} {
  return x;
}
