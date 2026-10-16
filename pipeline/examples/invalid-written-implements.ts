// A class's `implements` clause is an application with its bound: `any` is
// read as `unknown`, no `string`.
interface I<T extends string> {
  a: number;
}
export class C implements I<any> {
  a: number = 1;
}
