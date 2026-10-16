// `Extract<any, string>` is read as the declaration reader reads `any`,
// `unknown`: no value of `string`.
export function f(x: Extract<any, string>): string {
  return x;
}
