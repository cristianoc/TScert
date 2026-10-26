// A class declared with no body TypeScript checks: at run time the name may
// hold any constructor (`invalid-instanceof-ambient-value-import`).
declare module "@fixture/failures-ambient" {
  export class Declared {
    readonly declared: number;
  }
}
