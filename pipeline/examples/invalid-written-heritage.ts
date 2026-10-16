// An interface's `extends` clause is an application with its bound: `any`
// is read as `unknown`, no `string`.
interface I<T extends string> {
  a: number;
}
interface J extends I<any> {}
export function f(x: J): number {
  return x.a;
}
